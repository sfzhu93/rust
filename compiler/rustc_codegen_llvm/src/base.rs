//! Codegen the completed AST to the LLVM IR.
//!
//! Some functions here, such as codegen_block and codegen_expr, return a value --
//! the result of the codegen to LLVM -- while others, such as codegen_fn
//! and mono_item, are called only for the side effect of adding a
//! particular definition to the LLVM IR output we're producing.
//!
//! Hopefully useful general knowledge about codegen:
//!
//! * There's no way to find out the `Ty` type of a Value. Doing so
//!   would be "trying to get the eggs out of an omelette" (credit:
//!   pcwalton). You can, instead, find out its `llvm::Type` by calling `val_ty`,
//!   but one `llvm::Type` corresponds to many `Ty`s; for instance, `tup(int, int,
//!   int)` and `rec(x=int, y=int, z=int)` will have the same `llvm::Type`.

use super::ModuleLlvm;

use crate::attributes;
use crate::builder::Builder;
use crate::common;
use crate::context::CodegenCx;
use crate::llvm;
use crate::metadata;
use crate::value::Value;

use rustc_codegen_ssa::base::{maybe_create_entry_wrapper};
use rustc_codegen_ssa::mono_item::MonoItemExt;
use rustc_codegen_ssa::traits::*;
use rustc_codegen_ssa::{ModuleCodegen, ModuleKind};
use rustc_data_structures::small_c_str::SmallCStr;
use rustc_middle::dep_graph;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrs;
use rustc_middle::middle::cstore::EncodedMetadata;
use rustc_middle::middle::exported_symbols;
use rustc_middle::mir::mono::{Linkage, Visibility, MonoItem};
use rustc_middle::ty::TyCtxt;
//use rustc_middle::ty::{self, Instance, Ty, TypeFoldable};
use rustc_session::config::{DebugInfo, SanitizerSet};
use rustc_span::symbol::Symbol;
use tracing::debug;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use std::ffi::CString;
use std::time::Instant;
use rustc_middle::ty::layout::HasTyCtxt;
use rustc_target::abi::Align;

pub fn write_compressed_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    metadata: &EncodedMetadata,
    llvm_module: &mut ModuleLlvm,
) {
    use snap::write::FrameEncoder;
    use std::io::Write;

    let (metadata_llcx, metadata_llmod) = (&*llvm_module.llcx, llvm_module.llmod());
    let mut compressed = tcx.metadata_encoding_version();
    FrameEncoder::new(&mut compressed).write_all(&metadata.raw_data).unwrap();

    let llmeta = common::bytes_in_context(metadata_llcx, &compressed);
    let llconst = common::struct_in_context(metadata_llcx, &[llmeta], false);
    let name = exported_symbols::metadata_symbol_name(tcx);
    let buf = CString::new(name).unwrap();
    let llglobal =
        unsafe { llvm::LLVMAddGlobal(metadata_llmod, common::val_ty(llconst), buf.as_ptr()) };
    unsafe {
        llvm::LLVMSetInitializer(llglobal, llconst);
        let section_name = metadata::metadata_section_name(&tcx.sess.target.target);
        let name = SmallCStr::new(section_name);
        llvm::LLVMSetSection(llglobal, name.as_ptr());

        // Also generate a .section directive to force no
        // flags, at least for ELF outputs, so that the
        // metadata doesn't get loaded into memory.
        let directive = format!(".section {}", section_name);
        llvm::LLVMSetModuleInlineAsm2(metadata_llmod, directive.as_ptr().cast(), directive.len())
    }
}

pub struct ValueIter<'ll> {
    cur: Option<&'ll Value>,
    step: unsafe extern "C" fn(&'ll Value) -> Option<&'ll Value>,
}

impl Iterator for ValueIter<'ll> {
    type Item = &'ll Value;

    fn next(&mut self) -> Option<&'ll Value> {
        let old = self.cur;
        if let Some(old) = old {
            self.cur = unsafe { (self.step)(old) };
        }
        old
    }
}

pub fn iter_globals(llmod: &'ll llvm::Module) -> ValueIter<'ll> {
    unsafe { ValueIter { cur: llvm::LLVMGetFirstGlobal(llmod), step: llvm::LLVMGetNextGlobal } }
}

pub fn compile_codegen_unit(
    tcx: TyCtxt<'tcx>,
    cgu_name: Symbol,
) -> (ModuleCodegen<ModuleLlvm>, u64) {
    let prof_timer = tcx.prof.generic_activity_with_arg("codegen_module", cgu_name.to_string());
    let start_time = Instant::now();

    let dep_node = tcx.codegen_unit(cgu_name).codegen_dep_node(tcx);
    let (module, _) =
        tcx.dep_graph.with_task(dep_node, tcx, cgu_name, module_codegen, dep_graph::hash_result);
    let time_to_codegen = start_time.elapsed();
    drop(prof_timer);

    // We assume that the cost to run LLVM on a CGU is proportional to
    // the time we needed for codegenning it.
    let cost = time_to_codegen.as_secs() * 1_000_000_000 + time_to_codegen.subsec_nanos() as u64;

    fn make_func_wrapper_for_llfn(
        cx: &CodegenCx<'ll, 'tcx>,
        wrapper_name: &str,
        callee: &'ll Value,
    ) -> &'ll Value{
        //We only find the number of params, and generate void * params,
        //as we don't have an FFI API to get the return value of a function.
        //When the wrapped function is void?
        //consider add LLVMGetReturnType in llvm/lib/IR/Core.cpp to ffi

        let n_params = unsafe { llvm::LLVMCountParams(callee) } as usize;
        let mut wrapper_param_types = Vec::with_capacity(n_params + 1);
        let mut callee_type = common::val_ty(callee);
        while cx.type_kind(callee_type) == rustc_codegen_ssa::common::TypeKind::Pointer {
            callee_type = cx.element_type(callee_type);
        }//copied from check_call

        debug!("make_func_wrapper_for_llfn: callee_type={:?}", callee_type);
        let wrappee_param_types = cx.func_params_types(callee_type);
        for _ in 0..(n_params + 1) {
            wrapper_param_types.push(cx.type_ptr_to(cx.type_i8()));
        }
        let llfty = cx.type_func(&wrapper_param_types, cx.type_void());
        let llfn_wrapper = cx.declare_cfn(wrapper_name, llfty);
        debug!("make_func_wrapper_for_llfn: wrappee_param_types.len()={:?}", wrappee_param_types.len());
        let mut bx = Builder::new_block(&cx, llfn_wrapper, "start");
        let mut wrappee_params = Vec::with_capacity(n_params);
        for i in 0..n_params {
            let wrappee_type = wrappee_param_types[i];
            debug!("make_func_wrapper_for_llfn: wrappee_type={:?}", wrappee_type);
            let param_i = bx.bitcast(bx.get_param(i as usize),
                                     bx.type_ptr_to(wrappee_type));
            let param_i_imm = bx.load(param_i, Align::from_bytes(8).unwrap());
            wrappee_params.push(param_i_imm);
        }
        let callret = bx.call(callee, &wrappee_params, None);
        debug!("make_func_wrapper_for_llfn: callret={:?}", callret);
        let last_param = bx.get_param(n_params);
        debug!("make_func_wrapper_for_llfn: last_param={:?}", last_param);
        let _st = bx.store(callret,
                           last_param,
                           Align::from_bytes(8).unwrap());
        bx.ret_void();
        llfn_wrapper
    }

    fn make_func_wrappers(cx: &CodegenCx<'ll, 'tcx>) {
        let tcx = cx.tcx();
        let instances = cx.instances();
        for (_ins, _sym) in instances.borrow().iter() {
            let sym_name = tcx.symbol_name(*_ins).name;
            if sym_name.contains("ops..arith..Add") {
                debug!("compile_codegen_unit: make_func_wrappers: {:?}", sym_name);
                let llwrapper = make_func_wrapper_for_llfn(cx,
                                                           &sym_name.replace("Add", "Add_wrapper"),
                                                           _sym);
                cx.wrapper_funcs.borrow_mut().insert(_sym, llwrapper);
                //_sym.func_params_types(_sym);
                //TODO: can I read the generated LLVM code to know param types?
                //use func_params_types in src/type_.rs
                //add it to the wrappers' list
                //cx.wrapper_funcs.borrow_mut().insert(_sym, )
            }
        }
    }

    fn gen_fn2types(cx: &CodegenCx<'ll, 'tcx>) {
        let mut fn2types = FxHashMap::default();
        let mono_items = cx.codegen_unit.items_in_deterministic_order(cx.tcx);
        let tcx = cx.tcx;
        for &(mono_item, (_, _)) in &mono_items {
            if let MonoItem::Fn(instance) = mono_item {
                for elem in tcx.def_path(instance.def.def_id()).data {
                    debug!("gen_fn2types: elem in def_path={:?}", elem);
                    if let rustc_hir::definitions::DefPathData::Impl = elem.data {
                        debug!("it is an impl of a generic type");
                    }
                }
                fn2types.entry(instance.def).or_insert(Vec::new()).push(instance.substs);
            }
        }
        debug!("gen_fn2types: fn2types={:?}", fn2types);
    }

    fn is_type_ns_str(data: &rustc_hir::definitions::DefPathData, pattern: &str) -> bool {
        if let rustc_hir::definitions::DefPathData::TypeNs(sym) = data {
            if sym.as_str() == pattern {
                return true
            }
        }
        false
    }

    fn is_value_ns_str(data: &rustc_hir::definitions::DefPathData, pattern: &str) -> bool {
        if let rustc_hir::definitions::DefPathData::ValueNs(sym) = data {
            if sym.as_str() == pattern {
                return true
            }
        }
        false
    }

    fn is_start_or_exit_fn(cx: &CodegenCx<'ll, 'tcx>, instance: & rustc_middle::ty::Instance<'tcx>) -> bool {
        let tcx = cx.tcx;
        //let mut state_rust_begin_short_backtrace = 0;
        let def_id = instance.def.def_id();
        let crate_name = tcx.find_crate_name(def_id);
        //debug!("is_start_fn: {:?}", crate_name);
        let path_vec = tcx.def_path(def_id).data;
        debug!("is_start_fn: len(path_vec)={:?}", path_vec.len());
        if crate_name == "std" {
            debug!("is_start_fn: std");
            if path_vec.len() == 3 {
                debug!("is_start_fn: len=3, instance={:?}", instance);
                for dat in path_vec.iter() {
                    debug!("is_start_fn: {:?}", dat);
                }
                if is_type_ns_str(&path_vec[0].data, "sys_common")
                    && is_type_ns_str(&path_vec[1].data, "backtrace")
                    && is_value_ns_str(&path_vec[2].data, "__rust_begin_short_backtrace") {
                    //sys_common[0]::backtrace[0]::__rust_begin_short_backtrace[0]
                    return true;
                }
                if is_type_ns_str(&path_vec[0].data, "rt")
                    && is_value_ns_str(&path_vec[1].data, "lang_start") {
                    //rt[0]::lang_start[0]::{{closure}}[0]
                    debug!("is_start_fn:{:?}", path_vec[2].data);
                    if let rustc_hir::definitions::DefPathData::ClosureExpr = path_vec[2].data {
                        return true;
                    }
                }
            }
        }//TODO: add exit functions and closure in another function
        false
    }

    /*fn is_call_once_closure(cx: &CodegenCx<'ll, 'tcx>, instance: &rustc_middle::ty::Instance<'tcx>) -> bool {

    }*/

    fn gen_fn2trait_impl_instances(cx: &CodegenCx<'ll, 'tcx>) {
        let mut inst2trait_impl_instances = FxHashMap::default();
        let mono_items = cx.codegen_unit.items_in_deterministic_order(cx.tcx);
        let tcx = cx.tcx;
        for &(mono_item, (_, _)) in &mono_items {
            let instance = match mono_item { MonoItem::Fn(inst)  => inst, _ => continue };
            match instance.def {
                rustc_middle::ty::instance::InstanceDef::Item(..) => {},
                _ => continue
            }
            if is_start_fn(cx, &instance) {
                debug!("gen_fn2trait_impl_instances: is_start_fn: {:?}", instance);
                continue;
            }
            let mir = tcx.instance_mir(instance.def);

            for bb in mir.basic_blocks() {
                let terminator = match &bb.terminator { Some(te) => te, _ => continue};
                let func = match terminator.kind {
                    rustc_middle::mir::terminator::TerminatorKind::Call{ref func,..} => func, _ => continue
                };
                let constant = match *func {
                    rustc_middle::mir::Operand::Constant(ref constant) => constant,
                    _ => continue
                };
                let value = constant.literal.ty;
                let substs = match instance.substs_for_mir_body() {
                    Some(substs) => substs,
                    _ => continue
                };
                let subst_ty = &tcx.subst_and_normalize_erasing_regions(
                    substs,
                    rustc_middle::ty::ParamEnv::reveal_all(),
                    &value,
                );
                if let rustc_middle::ty::FnDef(def_id, subst) = subst_ty.kind() {
                    if let Some(..) = tcx.trait_of_item(*def_id) {
                        inst2trait_impl_instances.entry(instance).or_insert(FxHashSet::default()).insert(subst);
                        debug!("gen_fn2trait_impl_instances: {:?}, {:?}, {:?}", instance.def, def_id, subst);
                    }
                }
            }
        }
        debug!("gen_fn2trait_impl_instances: {:?}", inst2trait_impl_instances);
    }

    fn module_codegen(tcx: TyCtxt<'_>, cgu_name: Symbol) -> ModuleCodegen<ModuleLlvm> {
        let cgu = tcx.codegen_unit(cgu_name);
        // Instantiate monomorphizations without filling out definitions yet...
        let llvm_module = ModuleLlvm::new(tcx, &cgu_name.as_str());
        {
            let cx = CodegenCx::new(tcx, cgu, &llvm_module);
            gen_fn2types(&cx);
            gen_fn2trait_impl_instances(&cx);
            let mono_items = cx.codegen_unit.items_in_deterministic_order(cx.tcx);
            for &(mono_item, (linkage, visibility)) in &mono_items {
                mono_item.predefine::<Builder<'_, '_, '_>>(&cx, linkage, visibility);
            }

            // ... and now that we have everything pre-defined, fill out those definitions.
            for &(mono_item, _) in &mono_items {
                mono_item.define::<Builder<'_, '_, '_>>(&cx);
            }
            make_func_wrappers(&cx);
            //make_add_wrapper::<Builder<'_, '_, '_>>(&cx);

            // If this codegen unit contains the main function, also create the
            // wrapper here
            if let Some(entry) = maybe_create_entry_wrapper::<Builder<'_, '_, '_>>(&cx) {
                attributes::sanitize(&cx, SanitizerSet::empty(), entry);
            }

            // Run replace-all-uses-with for statics that need it
            for &(old_g, new_g) in cx.statics_to_rauw().borrow().iter() {
                unsafe {
                    let bitcast = llvm::LLVMConstPointerCast(new_g, cx.val_ty(old_g));
                    llvm::LLVMReplaceAllUsesWith(old_g, bitcast);
                    llvm::LLVMDeleteGlobal(old_g);
                }
            }

            // Finalize code coverage by injecting the coverage map. Note, the coverage map will
            // also be added to the `llvm.used` variable, created next.
            if cx.sess().opts.debugging_opts.instrument_coverage {
                cx.coverageinfo_finalize();
            }

            // Create the llvm.used variable
            // This variable has type [N x i8*] and is stored in the llvm.metadata section
            if !cx.used_statics().borrow().is_empty() {
                cx.create_used_variable()
            }

            // Finalize debuginfo
            if cx.sess().opts.debuginfo != DebugInfo::None {
                cx.debuginfo_finalize();
            }
        }

        ModuleCodegen {
            name: cgu_name.to_string(),
            module_llvm: llvm_module,
            kind: ModuleKind::Regular,
        }
    }

    (module, cost)
}

pub fn set_link_section(llval: &Value, attrs: &CodegenFnAttrs) {
    let sect = match attrs.link_section {
        Some(name) => name,
        None => return,
    };
    unsafe {
        let buf = SmallCStr::new(&sect.as_str());
        llvm::LLVMSetSection(llval, buf.as_ptr());
    }
}

pub fn linkage_to_llvm(linkage: Linkage) -> llvm::Linkage {
    match linkage {
        Linkage::External => llvm::Linkage::ExternalLinkage,
        Linkage::AvailableExternally => llvm::Linkage::AvailableExternallyLinkage,
        Linkage::LinkOnceAny => llvm::Linkage::LinkOnceAnyLinkage,
        Linkage::LinkOnceODR => llvm::Linkage::LinkOnceODRLinkage,
        Linkage::WeakAny => llvm::Linkage::WeakAnyLinkage,
        Linkage::WeakODR => llvm::Linkage::WeakODRLinkage,
        Linkage::Appending => llvm::Linkage::AppendingLinkage,
        Linkage::Internal => llvm::Linkage::InternalLinkage,
        Linkage::Private => llvm::Linkage::PrivateLinkage,
        Linkage::ExternalWeak => llvm::Linkage::ExternalWeakLinkage,
        Linkage::Common => llvm::Linkage::CommonLinkage,
    }
}

pub fn visibility_to_llvm(linkage: Visibility) -> llvm::Visibility {
    match linkage {
        Visibility::Default => llvm::Visibility::Default,
        Visibility::Hidden => llvm::Visibility::Hidden,
        Visibility::Protected => llvm::Visibility::Protected,
    }
}

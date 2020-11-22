use crate::context::CodegenCx;
use crate::value::Value;
use crate::llvm;
use crate::common;
use crate::builder::Builder;

use rustc_codegen_ssa::traits::*;
use rustc_data_structures::fx::{FxHashSet};//FxHashMap,
use rustc_middle::ty::{instance};
use rustc_middle::ty::layout::HasTyCtxt;
use rustc_target::abi::Align;
use tracing::debug;
use crate::mono_item::MonoItem;


fn make_func_wrapper_for_llfn(
    cx: &CodegenCx<'ll, 'tcx>,
    wrapper_name: &str,
    callee: &'ll Value,
) -> &'ll Value{
    //We only find the number of params, and generate void * params,
    //as we don't have an FFI API to get the return value of a function.
    //When the wrapped function is void?
    //consider add LLVMGetReturnType in llvm-project/llvm/include/llvm-c/Core.h to ffi

    let n_params = unsafe { llvm::LLVMCountParams(callee) } as usize;

    let mut wrapper_param_types = Vec::with_capacity(n_params + 1);
    let mut callee_type = common::val_ty(callee);
    while cx.type_kind(callee_type) == rustc_codegen_ssa::common::TypeKind::Pointer {
        callee_type = cx.element_type(callee_type);
    }//copied from check_call

    debug!("make_func_wrapper_for_llfn: callee_type={:?}", callee_type);
    let callee_ret_type = unsafe{ llvm::LLVMGetReturnType(callee_type)};
    debug!("make_func_wrapper_for_llfn: callee_ret_type={:?}", callee_ret_type);
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

pub(crate) fn make_func_wrappers(cx: &CodegenCx<'ll, 'tcx>) {
    let tcx = cx.tcx();
    let type2trait_impl_instances = cx.type2trait_impl_instances.borrow_mut();
    let instances = cx.instances();
    for (_ty, inst_set) in type2trait_impl_instances.iter() {
        //let inst_set = type2trait_impl_instances[&ty];
        for inst in inst_set.iter() {
            let sym = instances.borrow()[inst];
            let sym_name = tcx.symbol_name(*inst).name;
            let llwrapper = make_func_wrapper_for_llfn(cx,
   format!("{}{}", sym_name, "_wrapper").as_str(),
        sym);
            cx.wrapper_funcs.borrow_mut().insert(sym, llwrapper);
        }
    }
    /*for (_ins, _sym) in instances.borrow().iter() {
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
    }*/
}

pub(crate) fn gen_fn2types(cx: &CodegenCx<'ll, 'tcx>) {
    let mut fn2types = cx.fn2types.borrow_mut();
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
    if crate_name == "std" {
        if path_vec.len() == 3 {
            if is_type_ns_str(&path_vec[0].data, "sys_common")
                && is_type_ns_str(&path_vec[1].data, "backtrace")
                && is_value_ns_str(&path_vec[2].data, "__rust_begin_short_backtrace") {
                //sys_common[0]::backtrace[0]::__rust_begin_short_backtrace[0]
                return true;
            }
            if is_type_ns_str(&path_vec[0].data, "rt")
                && is_value_ns_str(&path_vec[1].data, "lang_start") {
                //rt[0]::lang_start[0]::{{closure}}[0]
                if let rustc_hir::definitions::DefPathData::ClosureExpr = path_vec[2].data {
                    return true;
                }
            }
            if is_type_ns_str(&path_vec[0].data, "process"){
                if let rustc_hir::definitions::DefPathData::Impl = &path_vec[1].data {
                    if is_value_ns_str(&path_vec[2].data, "report") {
                        return true;
                    }
                }
            }
        }
    }
    false
}

pub(crate) fn gen_fn2trait_impl_instances(cx: &CodegenCx<'ll, 'tcx>) {
    let mut inst2trait_impl_instances = cx.inst2trait_impl_instances.borrow_mut();
    let mut type2trait_impl_instances = cx.type2trait_impl_instances.borrow_mut();
    let mono_items = cx.codegen_unit.items_in_deterministic_order(cx.tcx);
    let tcx = cx.tcx;
    for &(mono_item, (_, _)) in &mono_items {
        let instance = match mono_item { MonoItem::Fn(inst)  => inst, _ => continue };
        match instance.def {
            instance::InstanceDef::Item(..) => {},
            _ => continue
        }//currently we only implement the most ordinary instances

        if is_start_or_exit_fn(cx, &instance) {
            debug!("gen_fn2trait_impl_instances: is_start_or_exit_fn: {:?}", instance);
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
                    debug!("gen_fn2trait_impl_instances: before resolving: {:?}, {:?}, {:?}", instance.def, def_id, subst);
                    let op_instance = rustc_middle::ty::Instance::resolve(tcx, rustc_middle::ty::ParamEnv::reveal_all(), *def_id, subst)
                        .unwrap()
                        .unwrap()
                        .polymorphize(tcx);
                    inst2trait_impl_instances.entry(instance)
                        .or_insert(FxHashSet::default()).insert(op_instance);
                    type2trait_impl_instances.entry(subst)
                        .or_insert(FxHashSet::default()).insert(op_instance);
                    debug!("gen_fn2trait_impl_instances: after resolving: {:?}, {:?}, {:?}", instance.def, def_id, subst);
                }
            }
        }
    }
    debug!("gen_fn2trait_impl_instances: {:?}", inst2trait_impl_instances);
    debug!("gen_fn2trait_impl_instances: {:?}", type2trait_impl_instances);
}
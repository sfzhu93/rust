use crate::abi::{FnAbi, FnAbiLlvmExt};
use crate::attributes;
use crate::base;
use crate::context::CodegenCx;
use crate::llvm;
use crate::type_of::LayoutLlvmExt;
use rustc_codegen_ssa::traits::*;
//use crate::value::Value;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
pub use rustc_middle::mir::mono::MonoItem;
use rustc_middle::mir::mono::{Linkage, Visibility};
use rustc_middle::ty::layout::FnAbiExt;
use rustc_middle::ty::{self, Instance, TypeFoldable};
use rustc_target::abi::LayoutOf;
use tracing::debug;

impl PreDefineMethods<'tcx> for CodegenCx<'ll, 'tcx> {
    fn predefine_static(
        &self,
        def_id: DefId,
        linkage: Linkage,
        visibility: Visibility,
        symbol_name: &str,
    ) {
        let instance = Instance::mono(self.tcx, def_id);
        let ty = instance.ty(self.tcx, ty::ParamEnv::reveal_all());
        let llty = self.layout_of(ty).llvm_type(self);

        let g = self.define_global(symbol_name, llty).unwrap_or_else(|| {
            self.sess().span_fatal(
                self.tcx.def_span(def_id),
                &format!("symbol `{}` is already defined", symbol_name),
            )
        });

        unsafe {
            llvm::LLVMRustSetLinkage(g, base::linkage_to_llvm(linkage));
            llvm::LLVMRustSetVisibility(g, base::visibility_to_llvm(visibility));
        }

        self.instances.borrow_mut().insert(instance, g);
    }

    fn predefine_fn_zsf(
        &self,
        instance: Instance<'tcx>,
        linkage: Linkage,
        visibility: Visibility,
        symbol_name: &str,
    ) {
        let symbol_name_zsf = format!("{}{}", symbol_name, "_dict_pass");//symbol_name.replace("8add_test17", "12add_test_zsf17");

        let fn_abi = FnAbi::of_instance(self, instance, &[]);//FnAbi::of_instance_zsf(self, instance, &[]);

        debug!("predefine_fn_zsf: fn_abi={:?}", fn_abi);
        //let lldecl = self.declare_fn(&symbol_name_zsf, &fn_abi);
        //TODO: use llvm codegen, instead of changing mir signature
        let llfntype = fn_abi.llvm_type(self);
        let n_params = unsafe {llvm::LLVMCountParamTypes(llfntype)} as usize;
        debug!("predefine_fn_zsf: n_params={:?}", n_params);
        let n_vtables = 1;
        let n_ret = 1;
        let mut original_param_types = Vec::with_capacity(n_params);
        unsafe {
            llvm::LLVMGetParamTypes(llfntype, original_param_types.as_mut_ptr());
            original_param_types.set_len(n_params);
        }
        let mut param_types = Vec::with_capacity(n_params + n_vtables + n_ret);
        for i in 0..n_params {
            debug!("predefine_fn_zsf: i={:?}", i);
            param_types.push(self.type_ptr_to(original_param_types[i]));
        }//why using one array gets a out of bound panic?

        param_types.push(self.type_ptr_to(self.type_i8()));
        let ret_type = unsafe{llvm::LLVMGetReturnType(llfntype)};
        param_types.push(self.type_ptr_to(self.type_ptr_to(ret_type)));
        let llfntype = self.type_func(&param_types, self.type_void());
        let lldecl = crate::declare::declare_raw_fn(self, symbol_name_zsf.as_str(), fn_abi.llvm_cconv(), llfntype);
        fn_abi.apply_attrs_llfn(self, lldecl);

        unsafe { llvm::LLVMRustSetLinkage(lldecl, base::linkage_to_llvm(linkage)) };
        let attrs = self.tcx.codegen_fn_attrs(instance.def_id());
        base::set_link_section(lldecl, &attrs);
        if linkage == Linkage::LinkOnceODR || linkage == Linkage::WeakODR {
            llvm::SetUniqueComdat(self.llmod, lldecl);
        }

        // If we're compiling the compiler-builtins crate, e.g., the equivalent of
        // compiler-rt, then we want to implicitly compile everything with hidden
        // visibility as we're going to link this object all over the place but
        // don't want the symbols to get exported.
        if linkage != Linkage::Internal
            && linkage != Linkage::Private
            && self.tcx.is_compiler_builtins(LOCAL_CRATE)
        {
            unsafe {
                llvm::LLVMRustSetVisibility(lldecl, llvm::Visibility::Hidden);
            }
        } else {
            unsafe {
                llvm::LLVMRustSetVisibility(lldecl, base::visibility_to_llvm(visibility));
            }
        }

        debug!("predefine_fn_zsf: instance = {:?}", instance);

        attributes::from_fn_attrs(self, lldecl, instance);

        self.instances_zsf.borrow_mut().insert(instance, lldecl);
    }

    fn predefine_fn(
        &self,
        instance: Instance<'tcx>,
        linkage: Linkage,
        visibility: Visibility,
        symbol_name: &str,
    ) {
        assert!(!instance.substs.needs_infer());
        let fn_abi = FnAbi::of_instance(self, instance, &[]);
        let lldecl = self.declare_fn(symbol_name, &fn_abi);
        unsafe { llvm::LLVMRustSetLinkage(lldecl, base::linkage_to_llvm(linkage)) };
        let attrs = self.tcx.codegen_fn_attrs(instance.def_id());
        base::set_link_section(lldecl, &attrs);
        if linkage == Linkage::LinkOnceODR || linkage == Linkage::WeakODR {
            llvm::SetUniqueComdat(self.llmod, lldecl);
        }

        // If we're compiling the compiler-builtins crate, e.g., the equivalent of
        // compiler-rt, then we want to implicitly compile everything with hidden
        // visibility as we're going to link this object all over the place but
        // don't want the symbols to get exported.
        if linkage != Linkage::Internal
            && linkage != Linkage::Private
            && self.tcx.is_compiler_builtins(LOCAL_CRATE)
        {
            unsafe {
                llvm::LLVMRustSetVisibility(lldecl, llvm::Visibility::Hidden);
            }
        } else {
            unsafe {
                llvm::LLVMRustSetVisibility(lldecl, base::visibility_to_llvm(visibility));
            }
        }

        debug!("predefine_fn: instance = {:?}", instance);

        attributes::from_fn_attrs(self, lldecl, instance);

        self.instances.borrow_mut().insert(instance, lldecl);
    }
}

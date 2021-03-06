use crate::base;
use crate::traits::*;
use rustc_hir as hir;
use rustc_middle::mir::mono::{Linkage, Visibility};
use rustc_middle::ty::layout::HasTyCtxt;

use rustc_middle::mir::mono::MonoItem;

pub trait MonoItemExt<'a, 'tcx> {
    fn define<Bx: BuilderMethods<'a, 'tcx>>(&self, cx: &'a Bx::CodegenCx);
    fn predefine<Bx: BuilderMethods<'a, 'tcx>>(
        &self,
        cx: &'a Bx::CodegenCx,
        linkage: Linkage,
        visibility: Visibility,
    );
    fn to_raw_string(&self) -> String;
}

impl<'a, 'tcx: 'a> MonoItemExt<'a, 'tcx> for MonoItem<'tcx> {
    fn define<Bx: BuilderMethods<'a, 'tcx>>(&self, cx: &'a Bx::CodegenCx) {
        debug!(
            "BEGIN IMPLEMENTING '{} ({})' in cgu {}",
            self,
            self.to_raw_string(),
            cx.codegen_unit().name()
        );

        match *self {
            MonoItem::Static(def_id) => {
                cx.codegen_static(def_id, cx.tcx().is_mutable_static(def_id));
            }
            MonoItem::GlobalAsm(hir_id) => {
                let item = cx.tcx().hir().expect_item(hir_id);
                if let hir::ItemKind::GlobalAsm(ref ga) = item.kind {
                    cx.codegen_global_asm(ga);
                } else {
                    span_bug!(item.span, "Mismatch between hir::Item type and MonoItem type")
                }
            }
            MonoItem::Fn(instance) => {
                /*if self.symbol_name(cx.tcx()).name.contains("8add_test17") {
                    base::codegen_instance_zsf::<Bx>(&cx, instance);
                    //add special case here
                    //remember to
                }*/
                base::codegen_instance::<Bx>(&cx, instance);
            }
        }

        debug!(
            "END IMPLEMENTING '{} ({})' in cgu {}",
            self,
            self.to_raw_string(),
            cx.codegen_unit().name()
        );
    }

    fn predefine<Bx: BuilderMethods<'a, 'tcx>>(
        &self,
        cx: &'a Bx::CodegenCx,
        linkage: Linkage,
        visibility: Visibility,
    ) {
        debug!(
            "BEGIN PREDEFINING '{} ({})' in cgu {}",
            self,
            self.to_raw_string(),
            cx.codegen_unit().name()
        );

        let symbol_name = self.symbol_name(cx.tcx()).name;

        debug!("symbol {}", &symbol_name);

        match *self {
            MonoItem::Static(def_id) => {
                cx.predefine_static(def_id, linkage, visibility, &symbol_name);
            }
            MonoItem::Fn(instance) => {
                if cx.should_dict_pass(&instance) {
                    debug!("predefine_fn: entering predefine_fn special case");
                    cx.predefine_fn_zsf(instance, linkage, visibility, symbol_name);
                }
                cx.predefine_fn(instance, linkage, visibility, &symbol_name);
            }
            MonoItem::GlobalAsm(..) => {}
        }

        debug!(
            "END PREDEFINING '{} ({})' in cgu {}",
            self,
            self.to_raw_string(),
            cx.codegen_unit().name()
        );
    }

    fn to_raw_string(&self) -> String {
        match *self {
            MonoItem::Fn(instance) => {
                format!("Fn({:?}, {})", instance.def, instance.substs.as_ptr() as usize)
            }
            MonoItem::Static(id) => format!("Static({:?})", id),
            MonoItem::GlobalAsm(id) => format!("GlobalAsm({:?})", id),
        }
    }
}

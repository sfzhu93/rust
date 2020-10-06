use rustc_middle::ty::{TyCtxt, TypeFolder, TyS, TypeFoldable};
use rustc_middle::ty;

struct TypePointerWrapper<'tcx>(TyCtxt<'tcx>);

impl TypeFolder<'tcx> for TypePointerWrapper<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.0
    }

    fn fold_ty(&mut self, t: &'tcx TyS<'tcx>) -> &'tcx TyS<'tcx> {
        match t.kind() {
            ty::Int(..) => {
                self.0.mk_imm_ptr(t)
            },
            _ => t.super_fold_with(self),
        }
    }
}
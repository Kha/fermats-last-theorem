import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt

set_option autoImplicit false
open scoped TensorProduct in

theorem HopfAlgebra.tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt
    (p : ℕ) (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (a b : H ⊗[GaloisRep.ratLocalizedAt p] H)
    (hab : ∀ f g : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) a =
        Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) b) :
    a = b := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt.solution

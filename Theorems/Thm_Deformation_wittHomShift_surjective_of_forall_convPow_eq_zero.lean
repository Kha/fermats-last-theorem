import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero

universe u v

theorem Deformation.wittHomShift_surjective_of_forall_convPow_eq_zero
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] (n : ℕ)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ n = 0)
    (m : ℕ) (hm : n ≤ m) :
    Function.Surjective (Deformation.wittHomShift k p m A) := by p2m_exact_reverting @_root_.P2MW.S_Deformation_wittHomShift_surjective_of_forall_convPow_eq_zero.solution

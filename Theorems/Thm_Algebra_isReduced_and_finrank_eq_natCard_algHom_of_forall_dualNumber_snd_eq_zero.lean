import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero

set_option autoImplicit false

theorem Algebra.isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    (h : ∀ (φ : R →ₐ[F] DualNumber Ω) (r : R), (φ r).snd = 0) :
    IsReduced R ∧ Module.finrank F R = Nat.card (R →ₐ[F] Ω) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isReduced_and_finrank_eq_natCard_algHom_of_forall_dualNumber_snd_eq_zero.solution

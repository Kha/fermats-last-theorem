import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (A : Divisor K F) {M : ℕ} (f : Fin M → F) (hf : LinearIndependent K f)
    (hfA : ∀ j, f j ∈ riemannRochSpace A)
    (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (hP : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational)
    (ht : ∀ i, (P i).ord (t i) = 1) (hA : ∀ i, A (P i) = 0) :
    IsUnit (jetMatrix P t e f).det ↔
      Submodule.span K (Set.range f) ⊓ riemannRochSpace (A - jetDivisor P) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot.solution

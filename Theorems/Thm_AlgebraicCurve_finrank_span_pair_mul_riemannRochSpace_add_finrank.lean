import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank

open AlgebraicCurve
theorem AlgebraicCurve.finrank_span_pair_mul_riemannRochSpace_add_finrank
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (L M : AlgebraicCurve.Divisor K F) {f₁ f₂ : F} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ w : AlgebraicCurve.Place K F, 0 ≤ w.ord f₁ + L w)
    (h₂ : ∀ w : AlgebraicCurve.Place K F, 0 ≤ w.ord f₂ + L w)
    (hbpf : ∀ w : AlgebraicCurve.Place K F, w.ord f₁ + L w = 0 ∨ w.ord f₂ + L w = 0)
    [FiniteDimensional K ↥(AlgebraicCurve.riemannRochSpace M)] :
    Module.finrank K ↥(Submodule.span K {f₁, f₂} * AlgebraicCurve.riemannRochSpace M)
        + Module.finrank K ↥(AlgebraicCurve.riemannRochSpace (M - L))
      = 2 * Module.finrank K ↥(AlgebraicCurve.riemannRochSpace M) ∧
    Submodule.span K {f₁, f₂} * AlgebraicCurve.riemannRochSpace M ≤ AlgebraicCurve.riemannRochSpace (M + L) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank.solution

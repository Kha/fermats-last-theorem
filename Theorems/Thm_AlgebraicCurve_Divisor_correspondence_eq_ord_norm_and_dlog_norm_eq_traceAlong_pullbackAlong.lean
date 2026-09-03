import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong

theorem AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong K ψ) (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hsep : AlgebraicCurve.SeparableAlong K ψ)
    (n : ℤ) (D : AlgebraicCurve.Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : AlgebraicCurve.Place K F, n * D v = v.ord f) :
    ∃ g : F, g = (letI := AlgebraicCurve.algebraAlong ψ; Algebra.norm F (φ f)) ∧ g ≠ 0 ∧
      (∀ v : AlgebraicCurve.Place K F,
        n * AlgebraicCurve.Divisor.correspondence φ ψ hφ hψ D v = v.ord g) ∧
      g⁻¹ • KaehlerDifferential.D K F g =
        AlgebraicCurve.Differential.traceAlong ψ
          (AlgebraicCurve.Differential.pullbackAlong φ (f⁻¹ • KaehlerDifferential.D K F f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong.solution

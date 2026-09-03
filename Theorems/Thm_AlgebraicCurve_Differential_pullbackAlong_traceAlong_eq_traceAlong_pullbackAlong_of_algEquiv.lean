import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv

theorem AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
    {K F F' F₀ F₀' : Type*} [Field K] [Field F] [Field F'] [Field F₀] [Field F₀']
    [Algebra K F] [Algebra K F'] [Algebra K F₀] [Algebra K F₀']
    (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (hsep : AlgebraicCurve.SeparableAlong K φ') (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (θ : F →ₐ[K] F₀) (AlgebraicCurve.Differential.traceAlong φ' η) =
      AlgebraicCurve.Differential.traceAlong φ (AlgebraicCurve.Differential.pullbackAlong (θ' : F' →ₐ[K] F₀') η) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv.solution

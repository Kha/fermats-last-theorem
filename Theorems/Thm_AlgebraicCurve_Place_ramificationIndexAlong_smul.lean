import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ramificationIndexAlong_smul

open AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndexAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_smul.solution

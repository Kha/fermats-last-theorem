import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv

theorem WeierstrassCurve.exists_addEquiv_point_baseChange_variableChange_smul_algEquiv {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] (W : WeierstrassCurve F) (γ : WeierstrassCurve.VariableChange F) : ∃ φ : ((γ • W).baseChange K).toAffine.Point ≃+ (W.baseChange K).toAffine.Point, ∀ (σ : K ≃ₐ[F] K) (P : ((γ • W).baseChange K).toAffine.Point), φ (σ • P) = σ • φ P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv.solution

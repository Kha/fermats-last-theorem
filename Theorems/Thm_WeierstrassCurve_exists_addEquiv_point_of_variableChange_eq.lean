import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.exists_addEquiv_point_of_variableChange_eq {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K] {E E' : WeierstrassCurve F} (C : VariableChange F) (hC : C • E = E') : ∃ e : (E⁄K).Point ≃+ (E'⁄K).Point, ∀ (σ : K ≃ₐ[F] K) (P : (E⁄K).Point), e (σ • P) = σ • e P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq.solution

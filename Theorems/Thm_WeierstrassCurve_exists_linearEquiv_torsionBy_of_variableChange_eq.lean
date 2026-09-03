import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_linearEquiv_torsionBy_of_variableChange_eq

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K] {E E' : WeierstrassCurve F} (C : VariableChange F) (hC : C • E = E') (n : ℕ) : ∃ φ : Submodule.torsionBy ℤ (E⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E'⁄K).Point n, ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E⁄K).Point n), φ (σ • x) = σ • φ x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_linearEquiv_torsionBy_of_variableChange_eq.solution

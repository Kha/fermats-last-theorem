import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.exists_linearEquiv_torsionBy_of_addEquiv {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] {E₁ E₂ : WeierstrassCurve F} (e : (E₁⁄K).Point ≃+ (E₂⁄K).Point) (he : ∀ (σ : K ≃ₐ[F] K) (P : (E₁⁄K).Point), e (σ • P) = σ • e P) (n : ℕ) : ∃ φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n, (∀ x : Submodule.torsionBy ℤ (E₁⁄K).Point n, (φ x : (E₂⁄K).Point) = e x) ∧ ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_exists_linearEquiv_torsionBy_of_addEquiv.solution

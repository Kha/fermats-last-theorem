import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.Affine.Point.galoisRepIsIrreducible_iff_of_linearEquiv {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K] [DecidableEq K] {E₁ E₂ : WeierstrassCurve F} {n : ℕ} (φ : Submodule.torsionBy ℤ (E₁⁄K).Point n ≃ₗ[ZMod n] Submodule.torsionBy ℤ (E₂⁄K).Point n) (hφ : ∀ (σ : K ≃ₐ[F] K) (x : Submodule.torsionBy ℤ (E₁⁄K).Point n), φ (σ • x) = σ • φ x) : GaloisRepIsIrreducible (K := K) F E₁ n ↔ GaloisRepIsIrreducible (K := K) F E₂ n := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv.solution

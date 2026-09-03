import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_galoisTrace_det_eq_of_isScalarTower

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.galoisTrace_det_eq_of_isScalarTower {R : Type*} [CommRing R] {F : Type*} [Field F] {k : Type*} [Field k] [DecidableEq k] {K : Type*} [Field K] [DecidableEq K] [Algebra R F] [Algebra R k] [Algebra R K] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower R F k] [IsScalarTower R F K] [IsScalarTower F k K] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k) (τ : K ≃ₐ[F] K) (hστ : ∀ x : k, τ (algebraMap k K x) = algebraMap k K (σ x)) (p : ℕ) [Fact p.Prime] (hk : Nat.card (Submodule.torsionBy ℤ (W⁄k).Point p) = p ^ 2) (hK : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) : galoisTrace F W p σ = galoisTrace F W p τ ∧ LinearMap.det (galoisRepModuleEnd F W p σ) = LinearMap.det (galoisRepModuleEnd F W p τ) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_galoisTrace_det_eq_of_isScalarTower.solution

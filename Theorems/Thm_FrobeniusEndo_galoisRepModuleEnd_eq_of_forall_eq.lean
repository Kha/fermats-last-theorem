import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
import P2M.Sol.S_FrobeniusEndo_galoisRepModuleEnd_eq_of_forall_eq

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo
theorem FrobeniusEndo.galoisRepModuleEnd_eq_of_forall_eq {R : Type*} [CommRing R] {S : Type*} [CommRing S] {S' : Type*} [CommRing S'] {k : Type*} [Field k] [DecidableEq k] [Algebra R S] [Algebra R S'] [Algebra R k] [Algebra S k] [Algebra S' k] [IsScalarTower R S k] [IsScalarTower R S' k] (W : WeierstrassCurve R) (σ : k ≃ₐ[S] k) (τ : k ≃ₐ[S'] k) (h : ∀ x : k, σ x = τ x) (p : ℕ) : galoisRepModuleEnd S W p σ = galoisRepModuleEnd S' W p τ ∧ galoisTrace S W p σ = galoisTrace S' W p τ ∧ LinearMap.det (galoisRepModuleEnd S W p σ) = LinearMap.det (galoisRepModuleEnd S' W p τ) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusEndo_galoisRepModuleEnd_eq_of_forall_eq.solution

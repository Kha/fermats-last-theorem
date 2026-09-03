import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import P2M.Util
namespace P2MW.S_MonoidHom_charpoly_apply_mul_mul_inv

theorem solution {R : Type*} {M : Type*} {G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Group G] (ρ : G →* Module.End R M) (σ τ : G) : (ρ (τ * σ * τ⁻¹)).charpoly = (ρ σ).charpoly := by
  let e : M ≃ₗ[R] M := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.toHomUnits τ)
  have he : e.conj (ρ σ) = ρ (τ * σ * τ⁻¹) := by
    rw [map_mul, map_mul]
    rfl
  rw [← he, LinearEquiv.charpoly_conj]

import Mathlib.LinearAlgebra.Charpoly.Basic
import P2M.Util
import P2M.Sol.S_MonoidHom_charpoly_apply_mul_mul_inv

theorem MonoidHom.charpoly_apply_mul_mul_inv {R : Type*} {M : Type*} {G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Group G] (ρ : G →* Module.End R M) (σ τ : G) : (ρ (τ * σ * τ⁻¹)).charpoly = (ρ σ).charpoly := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_charpoly_apply_mul_mul_inv.solution

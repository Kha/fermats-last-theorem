import Mathlib.RingTheory.Noetherian.Basic
import P2M.Util
import P2M.Sol.S_Module_Finite_of_ker_le_range_of_isNoetherianRing

theorem Module.Finite.of_ker_le_range_of_isNoetherianRing {R : Type*} [CommRing R] [IsNoetherianRing R] {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₁] [Module.Finite R N₂] (α : N₁ →ₗ[R] M) (β : M →ₗ[R] N₂) (h : LinearMap.ker β ≤ LinearMap.range α) : Module.Finite R M := by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing.solution

import Mathlib
import P2M.Util
namespace P2MW.S_LinearMap_exact_dualMap_of_exact

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem solution {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff] at h ⊢
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, h]
  ext ψ
  simp only [LinearMap.mem_ker, Submodule.mem_dualAnnihilator, LinearMap.mem_range]
  constructor
  · rintro hψ _ ⟨y, rfl⟩
    exact congrArg (fun χ : Module.Dual K V₁ => χ y) hψ
  · intro hψ
    ext y
    exact hψ _ ⟨y, rfl⟩

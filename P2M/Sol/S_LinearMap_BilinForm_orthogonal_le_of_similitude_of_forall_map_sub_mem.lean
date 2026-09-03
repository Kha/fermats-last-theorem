import Mathlib
import P2M.Util
namespace P2MW.S_LinearMap_BilinForm_orthogonal_le_of_similitude_of_forall_map_sub_mem

theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (hB : ∀ w : V, (∀ x : V, B x w = 0) → w = 0)
    (V₀ : Submodule K V) (g : V →ₗ[K] V) (hg : Function.Surjective g)
    (ε : K) (hε : ε ≠ 1)
    (hsim : ∀ x y : V, B (g x) (g y) = ε * B x y)
    (hmove : ∀ x : V, g x - x ∈ V₀) :
    B.orthogonal V₀ ≤ V₀ := by
  intro y hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy

  have hzV : g y - y ∈ V₀ := hmove y

  have hfix : ∀ x : V, B (g x) y = B x y := by
    intro x
    have h0 : B (g x - x) y = 0 := hy _ (hmove x)
    rw [map_sub, LinearMap.sub_apply] at h0
    exact sub_eq_zero.mp h0

  have key : ∀ x : V, B (g x) (ε • (g y - y) - (ε - 1) • g y) = 0 := by
    intro x
    rw [map_sub, map_smul, map_smul, map_sub, smul_eq_mul, smul_eq_mul, hsim x y, hfix x]
    ring

  have hzero : ε • (g y - y) - (ε - 1) • g y = 0 := by
    refine hB _ (fun w => ?_)
    obtain ⟨x, rfl⟩ := hg w
    exact key x
  have hne : ε - 1 ≠ 0 := sub_ne_zero.mpr hε
  have hgy : g y ∈ V₀ := by
    have h1 : (ε - 1) • g y = ε • (g y - y) := (sub_eq_zero.mp hzero).symm
    have h2 : g y = (ε - 1)⁻¹ • (ε • (g y - y)) := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h2]
    exact V₀.smul_mem _ (V₀.smul_mem _ hzV)
  have hy_eq : y = g y - (g y - y) := by abel
  rw [hy_eq]
  exact V₀.sub_mem hgy hzV

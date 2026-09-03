import Definitions.Def_ModularCurve_ComponentGroup
import P2M.Util
namespace P2MW.S_ModularCurve_gramMap_injective

open ModularCurve Finset

private theorem aux_eq_zero {ι : Type*} [Fintype ι] {e : ι → ℕ} (he : ∀ x, 0 < e x)
    {D : ι → ℤ} (h : widthPairing e D D = 0) : D = 0 := by
  rw [widthPairing_apply] at h
  have hterm : ∀ x ∈ Finset.univ, (0 : ℤ) ≤ (e x : ℤ) * (D x * D x) := fun x _ =>
    mul_nonneg (Int.natCast_nonneg _) (mul_self_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h
  funext x
  rcases mul_eq_zero.mp (hzero x (Finset.mem_univ x)) with hx | hx
  · exact absurd (Int.natCast_eq_zero.mp hx) (he x).ne'
  · exact mul_self_eq_zero.mp hx

theorem solution {ι : Type*} [Fintype ι] {e : ι → ℕ} (he : ∀ x, 0 < e x) :
    Function.Injective (gramMap e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  have hDD : widthPairing e D.1 D.1 = 0 := by
    have := congrArg (fun φ => φ D) hD
    simpa using this
  exact Subtype.ext (aux_eq_zero he hDD)

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic
import P2M.Util
import P2M.Sol.S_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le

theorem RegularSingular.norm_sum_shifted_sub_sum_reindexed_le
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d₂ : ℕ) (v : Fin (d₂ + 1) → Fin n → Fin J → E) (M : ℝ) (hM : ∀ a i j, ‖v a i j‖ ≤ M)
    (y : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    ‖(∑ a : Fin (d₂ + 1), ∑ i : Fin n, ∑ j : Fin J,
          ((y : ℂ) ^ (e i + (a : ℕ)) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • v a i j) -
        ∑ i' : Fin n, ∑ j : Fin J, ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) •
          (∑ a : Fin (d₂ + 1), ∑ i : Fin n, if e i + (a : ℕ) = e i' then v a i j else 0)‖ ≤
      (((d₂ : ℝ) + 1) * n * M * ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_norm_sum_shifted_sub_sum_reindexed_le.solution

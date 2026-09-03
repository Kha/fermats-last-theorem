import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_NumberField_exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow
    (K : Type) [Field K] [NumberField K] (w₀ : InfinitePlace K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : InfinitePlace K → ℝ) (R : ℝ), 0 ≤ R →
      {σ : InfinitePlace K → ℝ | σ w₀ = 0 ∧
        (∀ ε : (𝓞 K)ˣ, ∃ n : ℤ,
          ∑ v : InfinitePlace K, (v.mult : ℝ) * (σ v - a v) * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n) ∧
        ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |σ v - σ v'| ≤ R}.Finite ∧
      (({σ : InfinitePlace K → ℝ | σ w₀ = 0 ∧
        (∀ ε : (𝓞 K)ˣ, ∃ n : ℤ,
          ∑ v : InfinitePlace K, (v.mult : ℝ) * (σ v - a v) * Real.log (v (((ε : 𝓞 K)) : K)) = 2 * Real.pi * n) ∧
        ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |σ v - σ v'| ≤ R}.ncard : ℕ) : ℝ) ≤
        C * (1 + R) ^ (Fintype.card (InfinitePlace K) - 1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_forall_finite_and_ncard_setOf_sum_mult_mul_sub_mul_log_unit_le_mul_one_add_pow.solution

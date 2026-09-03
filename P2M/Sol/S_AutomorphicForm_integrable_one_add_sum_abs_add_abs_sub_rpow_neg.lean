import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import P2M.Util
namespace P2MW.S_AutomorphicForm_integrable_one_add_sum_abs_add_abs_sub_rpow_neg

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

namespace LCC1Proof

theorem main (V : Type) [Fintype V] [Nonempty V] (τ τ' : V → ℝ) (B : ℝ) (hB : 2 ≤ B) :
    MeasureTheory.Integrable (fun t : ℝ => (1 + ∑ v : V, (|t + τ v| + |t - τ' v|)) ^ (-B)) := by
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  have hg : Integrable (fun t : ℝ => (1 + ‖t + τ v₀‖) ^ (-B)) := by
    have h0 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-B)) := by
      refine integrable_one_add_norm ?_
      rw [Module.finrank_self]
      norm_num
      linarith
    exact h0.comp_add_right (τ v₀)
  have hbase_pos : ∀ t : ℝ, 0 < 1 + ∑ v : V, (|t + τ v| + |t - τ' v|) := fun t => by positivity
  have hcont : Continuous (fun t : ℝ => (1 + ∑ v : V, (|t + τ v| + |t - τ' v|)) ^ (-B)) := by
    refine Continuous.rpow_const ?_ (fun t => Or.inl (hbase_pos t).ne')
    fun_prop
  refine hg.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hbase_pos t).le _), Real.norm_eq_abs]
  have hsum : |t + τ v₀| + |t - τ' v₀| ≤ ∑ v : V, (|t + τ v| + |t - τ' v|) :=
    Finset.single_le_sum (f := fun v => |t + τ v| + |t - τ' v|) (fun v _ => by positivity) (Finset.mem_univ v₀)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [abs_nonneg (t - τ' v₀)]) (by linarith)

end LCC1Proof

theorem solution
    (V : Type) [Fintype V] [Nonempty V] (τ τ' : V → ℝ) (B : ℝ) (hB : 2 ≤ B) :
    MeasureTheory.Integrable
      (fun t : ℝ => (1 + ∑ v : V, (|t + τ v| + |t - τ' v|)) ^ (-B)) :=
  LCC1Proof.main V τ τ' B hB

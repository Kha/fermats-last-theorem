import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_constantTerm_smul
import P2M.Util
namespace P2MW.S_AutomorphicForm_IsCuspidalFn_smul
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : IsCuspidalFn μ u f) (c : ℂ) : IsCuspidalFn μ u (fun x => c * f x) :=
  fun g => by rw [constantTerm_smul, hf g, mul_zero]

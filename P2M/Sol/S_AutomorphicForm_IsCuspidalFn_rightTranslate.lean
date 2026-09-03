import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_constantTerm_rightTranslate
import P2M.Util
namespace P2MW.S_AutomorphicForm_IsCuspidalFn_rightTranslate
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : IsCuspidalFn μ u f) (h : G) : IsCuspidalFn μ u (fun x => f (x * h)) :=
  fun g => by rw [constantTerm_rightTranslate]; exact hf (g * h)

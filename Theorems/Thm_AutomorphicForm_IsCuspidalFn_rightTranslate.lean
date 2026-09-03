import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsCuspidalFn_rightTranslate
open AutomorphicForm MeasureTheory
theorem AutomorphicForm.IsCuspidalFn.rightTranslate
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : AutomorphicForm.IsCuspidalFn μ u f) (h : G) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => f (x * h)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsCuspidalFn_rightTranslate.solution

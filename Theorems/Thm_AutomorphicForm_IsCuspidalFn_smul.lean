import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsCuspidalFn_smul
open AutomorphicForm MeasureTheory
theorem AutomorphicForm.IsCuspidalFn.smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : AutomorphicForm.IsCuspidalFn μ u f) (c : ℂ) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => c * f x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsCuspidalFn_smul.solution

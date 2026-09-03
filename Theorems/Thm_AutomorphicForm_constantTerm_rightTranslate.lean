import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_constantTerm_rightTranslate
open AutomorphicForm MeasureTheory
theorem AutomorphicForm.constantTerm_rightTranslate
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) (f : G → ℂ) (g h : G) :
    AutomorphicForm.constantTerm μ u (fun x => f (x * h)) g
      = AutomorphicForm.constantTerm μ u f (g * h) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_constantTerm_rightTranslate.solution

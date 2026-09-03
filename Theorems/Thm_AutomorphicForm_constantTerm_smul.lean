import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_constantTerm_smul
open AutomorphicForm MeasureTheory
theorem AutomorphicForm.constantTerm_smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) (c : ℂ) (f : G → ℂ) (g : G) :
    AutomorphicForm.constantTerm μ u (fun x => c * f x) g
      = c * AutomorphicForm.constantTerm μ u f g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_constantTerm_smul.solution

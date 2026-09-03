import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_constantTerm_add
open AutomorphicForm MeasureTheory
theorem AutomorphicForm.constantTerm_add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₁ g) μ)
    (h₂ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₂ g) μ) :
    AutomorphicForm.constantTerm μ u (fun x => f₁ x + f₂ x) g
      = AutomorphicForm.constantTerm μ u f₁ g + AutomorphicForm.constantTerm μ u f₂ g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_constantTerm_add.solution

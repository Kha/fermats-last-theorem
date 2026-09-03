import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsCuspidalFn_add
open AutomorphicForm MeasureTheory
theorem AutomorphicForm.IsCuspidalFn.add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : MeasureTheory.Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : AutomorphicForm.IsCuspidalFn μ u f₁) (hf₂ : AutomorphicForm.IsCuspidalFn μ u f₂)
    (h₁ : ∀ g, MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₂ g) μ) :
    AutomorphicForm.IsCuspidalFn μ u (fun x => f₁ x + f₂ x) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsCuspidalFn_add.solution

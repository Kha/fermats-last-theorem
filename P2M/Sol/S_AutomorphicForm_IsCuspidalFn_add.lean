import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_constantTerm_add
import P2M.Util
namespace P2MW.S_AutomorphicForm_IsCuspidalFn_add
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : IsCuspidalFn μ u f₁) (hf₂ : IsCuspidalFn μ u f₂)
    (h₁ : ∀ g, Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, Integrable (constantTermIntegrand u f₂ g) μ) :
    IsCuspidalFn μ u (fun x => f₁ x + f₂ x) :=
  fun g => by rw [AutomorphicForm.constantTerm_add μ u g (h₁ g) (h₂ g), hf₁ g, hf₂ g, add_zero]

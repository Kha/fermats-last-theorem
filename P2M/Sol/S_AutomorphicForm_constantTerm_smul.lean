import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
namespace P2MW.S_AutomorphicForm_constantTerm_smul
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (c : ℂ) (f : G → ℂ) (g : G) :
    constantTerm μ u (fun x => c * f x) g = c * constantTerm μ u f g := by
  simpa [constantTerm, constantTermIntegrand, smul_eq_mul] using
    integral_smul (μ := μ) c (fun q => f (u q * g))

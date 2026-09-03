import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
namespace P2MW.S_AutomorphicForm_constantTerm_rightTranslate
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (f : G → ℂ) (g h : G) :
    constantTerm μ u (fun x => f (x * h)) g = constantTerm μ u f (g * h) := by
  simp only [constantTerm, constantTermIntegrand, mul_assoc]

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import P2M.Util
import P2M.Sol.S_NumberField_exists_isNonarchimedean_absoluteValue_extends

set_option autoImplicit false

theorem NumberField.exists_isNonarchimedean_absoluteValue_extends
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : NumberField.FinitePlace ↥L) :
    ∃ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ ∧
      ∀ a : ↥L, μ (a : AlgebraicClosure ℚ) = ν a := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isNonarchimedean_absoluteValue_extends.solution

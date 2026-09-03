import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import P2M.Util
import P2M.Sol.S_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq

set_option autoImplicit false

theorem NumberField.FinitePlace.exists_abs_log_le_mul_neg_log_of_coe_eq (z : AlgebraicClosure ℚ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → ν (p : ↥L) < 1 →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = z → |Real.log (ν a)| ≤ C * (-Real.log (ν (p : ↥L))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq.solution

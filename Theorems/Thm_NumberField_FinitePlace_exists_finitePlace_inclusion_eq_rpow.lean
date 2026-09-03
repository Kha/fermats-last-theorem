import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import P2M.Util
import P2M.Sol.S_NumberField_FinitePlace_exists_finitePlace_inclusion_eq_rpow

set_option autoImplicit false

theorem NumberField.FinitePlace.exists_finitePlace_inclusion_eq_rpow
    {L L' : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L] [NumberField ↥L'] (h : L ≤ L')
    (ν : NumberField.FinitePlace ↥L) :
    ∃ (ν' : NumberField.FinitePlace ↥L') (d : ℝ), 0 < d ∧
      ∀ x : ↥L, ν' (IntermediateField.inclusion h x) = ν x ^ d := by p2m_exact_reverting @_root_.P2MW.S_NumberField_FinitePlace_exists_finitePlace_inclusion_eq_rpow.solution

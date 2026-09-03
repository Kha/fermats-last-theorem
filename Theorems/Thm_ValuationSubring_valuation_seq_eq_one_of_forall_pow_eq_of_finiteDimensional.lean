import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import P2M.Util
import P2M.Sol.S_ValuationSubring_valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional
set_option autoImplicit false

theorem ValuationSubring.valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] {q : ℕ} (hq : 1 < q) (γ : ℕ → A.ValueGroup)
    (hK : ∀ n, ∃ x ∈ K, x ≠ 0 ∧ A.valuation x = γ n)
    (hstep : ∀ n, γ (n + 1) ^ q = γ n) :
    γ 0 = 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_valuation_seq_eq_one_of_forall_pow_eq_of_finiteDimensional.solution

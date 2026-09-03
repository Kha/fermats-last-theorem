import Mathlib
import P2M.Util
import P2M.Sol.S_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable

theorem Field.exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable
    {M E : Type*} [Field M] [Field E] [Algebra M E] [FiniteDimensional M E]
    [IsPurelyInseparable M E] (p : ℕ) [Fact p.Prime] [CharP E p]
    (hp : Module.finrank (frobenius E p).fieldRange E = p) :
    ∃ r : ℕ, Module.finrank M E = p ^ r ∧
      (algebraMap M E).fieldRange = (iterateFrobenius E p r).fieldRange := by p2m_exact_reverting @_root_.P2MW.S_Field_exists_finrank_eq_pow_and_fieldRange_eq_iterateFrobenius_of_isPurelyInseparable.solution

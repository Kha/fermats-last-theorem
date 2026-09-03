import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three

theorem NumberField.count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three
    (K : Type) [Field K] [NumberField K] (P : Ideal (NumberField.RingOfIntegers K))
    (hP : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(3 : ℤ)}) (NumberField.RingOfIntegers K)) :
    (UniqueFactorizationMonoid.normalizedFactors
        (differentIdeal ℤ (NumberField.RingOfIntegers K))).count P
      ≤ (Ideal.span {(3 : ℤ)}).ramificationIdx' P
        + (Ideal.span {(3 : ℤ)}).ramificationIdx' P
          * padicValNat 3 ((Ideal.span {(3 : ℤ)}).ramificationIdx' P) - 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.solution

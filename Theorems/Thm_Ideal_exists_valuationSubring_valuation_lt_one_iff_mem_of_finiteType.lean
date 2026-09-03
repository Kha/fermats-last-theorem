import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType

set_option autoImplicit false

universe u v w

theorem Ideal.exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    ∃ (O : ValuationSubring K) (d : ℕ) (f : Fin d → K),
      O ≠ ⊤ ∧ (∀ a : A, algebraMap A K a ∈ O) ∧
      (∀ a : A, O.valuation (algebraMap A K a) < 1 ↔ a ∈ p) ∧
      ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A ∧
      (∀ i, f i ∈ O) ∧
      ∀ Q : MvPolynomial (Fin d) k, O.valuation (MvPolynomial.aeval f Q) < 1 → Q = 0 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType.solution

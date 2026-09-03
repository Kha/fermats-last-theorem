import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_eq_of_forall_exists_sub_valuation_lt_one

set_option autoImplicit false

theorem ValuationSubring.eq_of_forall_exists_sub_valuation_lt_one
    {K M O : Type*} [Field K] [Field M] [Algebra K M]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (hKO : ∀ c : K, algebraMap K M c ∈ (algebraMap O M).range)
    (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (hgen : Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) = ⊤)
    (V V' : ValuationSubring M) (hOV : ∀ b : O, algebraMap O M b ∈ V) (hOV' : ∀ b : O, algebraMap O M b ∈ V')
    (hdom : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O →
      V.valuation (algebraMap O M b) < 1 ∧ V'.valuation (algebraMap O M b) < 1)
    (hval : ∀ b : O, ∃ c : M, c ∈ E ∧
      V.valuation (algebraMap O M b - c) < 1 ∧ V'.valuation (algebraMap O M b - c) < 1) :
    V = V' := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_eq_of_forall_exists_sub_valuation_lt_one.solution

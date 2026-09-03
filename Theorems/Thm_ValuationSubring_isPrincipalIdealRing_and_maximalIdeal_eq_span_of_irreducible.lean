import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible

set_option autoImplicit false

theorem ValuationSubring.isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible
    {K M O : Type*} [Field K] [Field M] [Algebra K M]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O M]
    (hinj : Function.Injective (algebraMap O M))
    (hKO : ∀ c : K, algebraMap K M c ∈ (algebraMap O M).range)
    (E : Subfield M) (hE : ∀ x ∈ E, IsSeparable K x)
    (hgen : Subfield.closure (((algebraMap O M).range : Set M) ∪ (E : Set M)) = ⊤)
    (V : ValuationSubring M) (hOV : ∀ b : O, algebraMap O M b ∈ V)
    (hdom : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O → V.valuation (algebraMap O M b) < 1)
    (π : O) (hπ : Irreducible π) :
    IsPrincipalIdealRing ↥V ∧ V ≠ ⊤ ∧
      IsLocalRing.maximalIdeal ↥V = Ideal.span {(⟨algebraMap O M π, hOV π⟩ : ↥V)} := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isPrincipalIdealRing_and_maximalIdeal_eq_span_of_irreducible.solution

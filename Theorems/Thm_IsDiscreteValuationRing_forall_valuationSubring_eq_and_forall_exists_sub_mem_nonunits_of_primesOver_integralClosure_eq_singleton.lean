import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton

set_option autoImplicit false

theorem IsDiscreteValuationRing.forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (E : Type*) [Field E] [Algebra O E]
    [IsDedekindDomain ↥(integralClosure O E)] [Module.Finite O ↥(integralClosure O E)]
    [IsFractionRing ↥(integralClosure O E) E]
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ)
    (𝔓 : Ideal ↥(integralClosure O E)) [h𝔓 : 𝔓.IsPrime] (h0 : 𝔓 ≠ ⊥)
    (hover : (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O E) = {𝔓})
    (he : (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = n)
    (hf : (IsLocalRing.maximalIdeal O).inertiaDeg' 𝔓 = 1)
    (W : ValuationSubring E)
    (hW : W = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E ⟨𝔓, h𝔓, h0⟩) :

    (∀ W₁ W₂ : ValuationSubring E,
        (∀ x : O, algebraMap O E x ∈ W₁) → (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O E x ∈ W₁.nonunits) →
        (∀ x : O, algebraMap O E x ∈ W₂) → (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O E x ∈ W₂.nonunits) →
        W₁ = W₂) ∧

    (∀ x : O, algebraMap O E x ∈ W) ∧
    (∀ x : O, algebraMap O E x ∈ W.nonunits ↔ x ∈ IsLocalRing.maximalIdeal O) ∧

    (∀ e : ↥W, ∃ f : O, (e : E) - algebraMap O E f ∈ W.nonunits) ∧

    (∃ (π : ↥W) (v : (↥W)ˣ), Irreducible π ∧
      algebraMap O E ϖ = ((v : ↥W) : E) * ((π : ↥W) : E) ^ n) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton.solution

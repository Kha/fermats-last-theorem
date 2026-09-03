import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
set_option autoImplicit false

theorem IsDiscreteValuationRing.primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    (E : Type*) [Field E] [Algebra O E] [IsFractionRing O E] [Algebra E F]
    [IsScalarTower O E F] [FiniteDimensional E F] [Algebra.IsSeparable E F]
    [IsDedekindDomain ↥(integralClosure O F)] [Module.Finite O ↥(integralClosure O F)]
    [IsFractionRing ↥(integralClosure O F) F]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔓 : ι → Ideal ↥(integralClosure O F))
    [hprime : ∀ i, (𝔓 i).IsPrime] (h0 : ∀ i, 𝔓 i ≠ ⊥) [hover : ∀ i, (𝔓 i).LiesOver (IsLocalRing.maximalIdeal O)]
    (hinj : Function.Injective 𝔓)
    (d : ι → ℕ) (hd : ∀ i, d i ≤ (IsLocalRing.maximalIdeal O).inertiaDeg' (𝔓 i)) (hsum : Module.finrank E F ≤ ∑ i, d i) :
    (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O F) = Set.range 𝔓 ∧
    (∀ i, Ideal.ramificationIdx' (IsLocalRing.maximalIdeal O) (𝔓 i) = 1) ∧
    (∀ i, (IsLocalRing.maximalIdeal O).inertiaDeg' (𝔓 i) = d i) ∧
    (∑ i, d i = Module.finrank E F) ∧
    (∀ V' : ValuationSubring F, V' ≠ ⊤ → (∀ x : O, algebraMap O F x ∈ V') →
        (∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O F x ∈ V'.nonunits) →
        ∃ i, V' = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩) ∧
    (∀ i, ∀ ϖ : O, Irreducible ϖ → ∀ x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩,
        x ∈ (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩).nonunits →
        ∃ y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓 i, hprime i, h0 i⟩, x = algebraMap O F ϖ * y) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg.solution

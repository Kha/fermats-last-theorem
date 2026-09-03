import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ideal_integralClosure_eq_valuationSubringAtPrime_and_inertiaDeg_eq_finrank

set_option autoImplicit false

theorem ValuationSubring.exists_ideal_integralClosure_eq_valuationSubringAtPrime_and_inertiaDeg_eq_finrank
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    [IsDedekindDomain ↥(integralClosure O F)] [IsFractionRing ↥(integralClosure O F) F]
    (W : ValuationSubring F) (hOW : ∀ x : O, algebraMap O F x ∈ W)
    (hmW : ∀ x ∈ IsLocalRing.maximalIdeal O, algebraMap O F x ∈ W.nonunits)
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (red : ↥W →+* Ω) (hker : RingHom.ker red = IsLocalRing.maximalIdeal ↥W)
    (K₀ K : IntermediateField k Ω)
    (hK₀ : ∀ z : Ω, z ∈ K₀ ↔ ∃ x : O, red ⟨algebraMap O F x, hOW x⟩ = z)
    (hK : ∀ z : Ω, z ∈ K ↔ ∃ w : ↥W, red w = z) :
    ∃ (𝔓 : Ideal ↥(integralClosure O F)) (h𝔓 : 𝔓.IsPrime) (h0 : 𝔓 ≠ ⊥),
      (∀ b : ↥(integralClosure O F), b ∈ 𝔓 ↔ ((b : F) ∈ W.nonunits)) ∧
      𝔓.LiesOver (IsLocalRing.maximalIdeal O) ∧
      W = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F ⟨𝔓, h𝔓, h0⟩ ∧
      ∃ hle : K₀ ≤ K, (IsLocalRing.maximalIdeal O).inertiaDeg' 𝔓 =
        Module.finrank ↥K₀ ↥(IntermediateField.extendScalars hle) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ideal_integralClosure_eq_valuationSubringAtPrime_and_inertiaDeg_eq_finrank.solution

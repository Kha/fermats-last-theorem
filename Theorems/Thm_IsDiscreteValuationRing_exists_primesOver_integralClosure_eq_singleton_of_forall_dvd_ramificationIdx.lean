import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (F : Type*) [Field F] [Algebra O F] [IsFractionRing O F]
    (E : Type*) [Field E] [Algebra F E] [Algebra O E] [IsScalarTower O F E]
    [FiniteDimensional F E]
    [IsDedekindDomain ↥(integralClosure O E)] [Module.Finite O ↥(integralClosure O E)]
    [IsFractionRing ↥(integralClosure O E) E]
    (n : ℕ) (hn : Module.finrank F E ≤ n)
    (hdvd : ∀ (𝔓 : Ideal ↥(integralClosure O E)) [𝔓.IsPrime], 𝔓 ≠ ⊥ →
      𝔓.LiesOver (IsLocalRing.maximalIdeal O) → n ∣ (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓) :
    ∃ (𝔓 : Ideal ↥(integralClosure O E)), 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧
      (IsLocalRing.maximalIdeal O).primesOver ↥(integralClosure O E) = {𝔓} ∧
      (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = n ∧
      (IsLocalRing.maximalIdeal O).inertiaDeg' 𝔓 = 1 ∧
      Module.finrank F E = n := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_primesOver_integralClosure_eq_singleton_of_forall_dvd_ramificationIdx.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx

set_option autoImplicit false

theorem Ideal.map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx
    {R S F : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] [Field F]
    [Algebra R S] [Module.IsTorsionFree R S] [Algebra S F] [IsFractionRing S F]
    (p : Ideal R) (hp : p ≠ ⊥) (𝔓 : Ideal S) [𝔓.IsMaximal] [𝔓.LiesOver p]
    (P : ValuationSubring F)
    (hSP : ∀ s : S, algebraMap S F s ∈ P)
    (hcent : ∀ s : S, algebraMap S F s ∈ P.nonunits ↔ s ∈ 𝔓)
    (hfrac : ∀ e : ↥P, ∃ s t : S, t ∉ 𝔓 ∧ (e : F) * algebraMap S F t = algebraMap S F s)
    (φ : R →+* ↥P) (hφ : ∀ r : R, ((φ r : ↥P) : F) = algebraMap S F (algebraMap R S r)) :
    Ideal.map φ p = IsLocalRing.maximalIdeal ↥P ^ Ideal.ramificationIdx' p 𝔓 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_valuationSubring_eq_maximalIdeal_pow_ramificationIdx.solution

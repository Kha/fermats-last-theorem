import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_unique_centred_of_isDiscreteValuationRing_of_isFractionRing

set_option autoImplicit false

theorem ValuationSubring.exists_unique_centred_of_isDiscreteValuationRing_of_isFractionRing
    {B : Type*} [CommRing B] {F : Type*} [Field F]
    (ρ : B →+* F) (𝔶 : Ideal B) [𝔶.IsMaximal] (hker : RingHom.ker ρ ≤ 𝔶)
    (R : Subring F)
    (hR : ∀ x : F, x ∈ R ↔ ∃ s t : B, t ∉ 𝔶 ∧ x * ρ t = ρ s)
    (hdvr : IsDiscreteValuationRing ↥R) (hfrac : IsFractionRing ↥R F) :
    ∃ P : ValuationSubring F,
      (∀ s : B, ρ s ∈ P) ∧
      (∀ s : B, ρ s ∈ P.nonunits ↔ s ∈ 𝔶) ∧
      (∀ P' : ValuationSubring F,
        (∀ s : B, ρ s ∈ P') → (∀ s : B, ρ s ∈ P'.nonunits ↔ s ∈ 𝔶) → P' = P) ∧
      (∀ e : ↥P, ∃ s : B, (e : F) - ρ s ∈ P.nonunits) ∧
      IsPrincipalIdealRing ↥P := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_unique_centred_of_isDiscreteValuationRing_of_isFractionRing.solution

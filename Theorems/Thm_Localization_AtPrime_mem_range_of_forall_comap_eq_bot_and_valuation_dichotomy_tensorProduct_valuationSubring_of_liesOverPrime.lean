import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_Localization_AtPrime_mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime

set_option autoImplicit false

open IsLocalRing
open scoped TensorProduct

theorem Localization.AtPrime.mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))

    [Algebra ↥(GaloisRep.ratLocalizedAt p) ↥Pl] (halg : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥Pl = ρ)
    (B : Type) [CommRing B] [Algebra ↥(GaloisRep.ratLocalizedAt p) B]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt p) B] [Module.Flat ↥(GaloisRep.ratLocalizedAt p) B]
    (𝔔 : Ideal (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B)) [𝔔.IsPrime]
    (h𝔔 : 𝔔.comap (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom =
      maximalIdeal ↥Pl)
    [IsDomain (Localization.AtPrime 𝔔)]
    (h𝔭 : ((maximalIdeal ↥Pl).map ((algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) (Localization.AtPrime 𝔔)).comp
        (Algebra.TensorProduct.includeLeft
          (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom)).IsPrime)
    (K : Type) [Field K] [Algebra (Localization.AtPrime 𝔔) K] [IsFractionRing (Localization.AtPrime 𝔔) K] :
    letI S := Localization.AtPrime 𝔔
    letI toS : ↥Pl →+* S := (algebraMap (↥Pl ⊗[↥(GaloisRep.ratLocalizedAt p)] B) S).comp
      (Algebra.TensorProduct.includeLeft
        (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥(GaloisRep.ratLocalizedAt p)) (A := ↥Pl) (B := B)).toRingHom
    letI 𝔭 : Ideal S := (maximalIdeal ↥Pl).map toS

    (∀ h : K,
      (∃ a c : S, c ∉ 𝔭 ∧ h * algebraMap S K c = algebraMap S K a) →
      (∀ 𝔮 : Ideal S, 𝔮.IsPrime → 𝔮.comap toS = ⊥ →
        ∃ a s : S, s ∉ 𝔮 ∧ h * algebraMap S K s = algebraMap S K a) →
      h ∈ Set.range (algebraMap S K)) ∧

    (∀ h : K,
      (∃ a c : S, c ∉ 𝔭 ∧ h * algebraMap S K c = algebraMap S K a) ∨
      (∃ a c : S, c ∉ 𝔭 ∧ h⁻¹ * algebraMap S K c = algebraMap S K a)) := by p2m_exact_reverting @_root_.P2MW.S_Localization_AtPrime_mem_range_of_forall_comap_eq_bot_and_valuation_dichotomy_tensorProduct_valuationSubring_of_liesOverPrime.solution

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.SUnits.isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)) [Fintype B] (hB : ∀ b : B, p • b = 0)
    (h1 : (Rep.homSeq₁ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).ShortExact)
    (ιE : (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    {ΛE : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)

    (η : groupCohomology (Rep.defectQ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) 1)
    (c : cocycles₂ ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (hc : (H2π ((ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ))).hom c = (groupCohomology.δ h1 1 2 rfl).hom η)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : ∀ (γ₁ γ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B), κ b (m (γ₁, γ₂)) =
      ιE (LinearMap.toAddMonoidHom ((c : (↥F ≃ₐ[ℚ] ↥F) × (↥F ≃ₐ[ℚ] ↥F) → (ihom B).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) (AlgEquiv.restrictNormalHom ↥F γ₁, AlgEquiv.restrictNormalHom ↥F γ₂)) b))
    (hmS : m ∈ levelCocyclesS₂ S M) :
    ΛE ((groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F)) (Rep.homSeq₂ B (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)).f 1).hom η) = continuousH2Sπ S M ⟨m, hmS⟩ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_isGlobalBridge2_apply_map_homSeq_f_eq_continuousH2Spi_of_eq_delta.solution

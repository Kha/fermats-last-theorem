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
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
attribute [-instance] AlgebraicClosure.Rat.isGalois
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk Rep.coe_tateδneg2_apply groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain ExtCitation open groupCohomology hiding exists_isGlobalBridge2
open scoped NumberField.PlaceDecomp

theorem NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S)
    (hFM : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m)
    (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] (hB : ∀ b : B, p • b = 0)

    (ιE₁ : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₁ : ∀ x, Additive.toMul (ιE₁ x) = Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ x))
    (hμ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ, ιE₁ e = Additive.ofMul u)

    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)

    {Λ₁ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →+ continuousH2S S M}
    (hΛ₁ : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F₁) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE₁ κ Λ₁) :
    ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₂ ∧ FiniteDimensional ℚ ↥F₂ ∧ IsGalois ℚ ↥F₂ ∧ F₂.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] [IsGalois ℚ ↥F₃] (_ : F₂ ≤ F₃)
        (π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
        (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
        (ιE₃ : NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
        (_ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ x))
        (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ)
        (_ : ∀ x, ιE₃ (jE.hom x) = ιE₁ x)
        (x : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) (_ : Λ₁ x = 0),
        (groupCohomology.map π (Rep.extInflR π B (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ) jE) 1).hom x = 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero.solution

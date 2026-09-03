import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow
attribute [-instance] AlgebraicClosure.Rat.isGalois
attribute [-simp] groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk
set_option autoImplicit false
open NumberField hiding exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one open IsDedekindDomain ExtCitation

theorem NumberField.SUnits.exists_sLevel_forall_sUnitsRep_map_val_eq_pow
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S) :
    ∃ F₁' : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₁' ∧ FiniteDimensional ℚ ↥F₁' ∧ IsGalois ℚ ↥F₁' ∧ F₁'.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] (_ : F₁' ≤ F₃)
        (e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ),
        ∃ e' : NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ,
          Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ e) =
            (Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ e')) ^ p := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow.solution

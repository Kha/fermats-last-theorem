import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem
attribute [-instance] NumberField.LevelArith.instCommGroupUnitsModPow
attribute [-simp] groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation IsDedekindDomain M4aHerbrand NumberField.LevelArith open NumberField hiding exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem
open scoped NumberField.LevelArith NumberField.PlaceDecomp
open scoped NumberField.InfPlaceDecomp

theorem NumberField.LevelArith.exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) :
    ∃ (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hfd : FiniteDimensional ℚ ↥F₂) (_ : F₂.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F₂)
      (hFF₂ : F ≤ F₂),
      haveI := hfd
      ∀ [Algebra ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))],
        (∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂)) x : ↥(levelField L F₂ (hLF.trans hFF₂))) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) →
        ∀ z : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ,
          (∃ k : ℕ, z ^ p ^ k ∈ ((M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)})) →
          Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F₂ (hLF.trans hFF₂))).β.toMonoidHom z ∈ ((M4aHerbrand.principalIdeles (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂))) ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 ↥(levelField L F₂ (hLF.trans hFF₂))) ↥(levelField L F₂ (hLF.trans hFF₂)) {w | w.under (𝓞 ↥L) ∈ (placesOverPrimesFinset ↥L S)}) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_le_unitsMap_genuineBaseChange_mem_sup_of_pow_mem.solution

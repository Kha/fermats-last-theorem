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
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_mem_placesOverPrimesFinset_pow_dvd_natCard_decomp_above_of_isPGroup_of_not_dvd
attribute [-simp] NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_mem_placesOverPrimesFinset_pow_dvd_natCard_decomp_above_of_isPGroup_of_not_dvd
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L L₁ F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F : L₁ ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    (hP : IsPGroup p (↥L₁.fixingSubgroup ⧸ F.fixingSubgroup.comap L₁.fixingSubgroup.subtype))
    (hcop : ¬ p ∣ Module.finrank ↥L ↥(levelField L L₁ hLL₁))
    (k : ℕ)
    (hk : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField L F hLF)),
      w ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L F hLF) (S : Set Nat.Primes) →
      p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) :
    ∃ v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L₁),
      v₀ ∈ placesOverPrimesFinset ↥L₁ S ∧
      p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L₁ ↥(levelField L₁ F hL₁F) (NumberField.PlaceAbove.above ↥L₁ ↥(levelField L₁ F hL₁F) v₀)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_mem_placesOverPrimesFinset_pow_dvd_natCard_decomp_above_of_isPGroup_of_not_dvd.solution

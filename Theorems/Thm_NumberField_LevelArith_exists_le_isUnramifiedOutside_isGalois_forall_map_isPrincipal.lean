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
import P2M.Sol.S_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal
attribute [-instance] NumberField.LevelArith.instCommGroupUnitsModPow
attribute [-simp] groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith~exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span"
p2m_open "scoped NumberField.LevelArith~exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span NumberField.PlaceDecomp"

theorem NumberField.LevelArith.exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) :
    ∃ (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : F ≤ F'') (_ : FiniteDimensional ℚ ↥F''),
      F''.IsUnramifiedOutside S ∧ IsGalois ℚ ↥F'' ∧
      ∀ (I : Ideal (𝓞 ↥F)) (k : ℕ) (a : 𝓞 ↥F), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
        (I.map (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom)).IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_le_isUnramifiedOutside_isGalois_forall_map_isPrincipal.solution

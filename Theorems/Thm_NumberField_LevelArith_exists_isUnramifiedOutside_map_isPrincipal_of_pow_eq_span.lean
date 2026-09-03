import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span
attribute [-instance] NumberField.LevelArith.instCommGroupUnitsModPow
attribute [-simp] NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.SUnits.val_zsmul NumberField.SUnits.val_add groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk

set_option autoImplicit false
open NumberField ExtCitation

theorem NumberField.LevelArith.exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (I : Ideal (𝓞 ↥F)) (k : ℕ) (a : 𝓞 ↥F) (ha : a ≠ 0) (hI : I ^ p ^ k = Ideal.span {a}) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : F ≤ F'), F'.IsUnramifiedOutside S ∧
      (I.map (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom)).IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span.solution

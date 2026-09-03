import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_NumberField_SUnitsMax
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup groupCohomology.instMulDistribMulActionGaloisSUnits
attribute [-simp] groupCohomology.coe_smul_galoisSUnits groupCohomology.galoisSUnitsToUnits_apply

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation NumberField.LevelArith

theorem groupCohomology.mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hD : D ≤ F.fixingSubgroup)
    (X : ↥D × ↥D → sUnitsMaxRep S F)
    (hX : X ∈ levelCocycles₂ D.subtype (Rep.res (Subgroup.inclusion hD) (sUnitsMaxRep S F)))
    (hpX : (p : ℤ) • X ∈ levelCoboundaries₂ D.subtype (Rep.res (Subgroup.inclusion hD) (sUnitsMaxRep S F)))
    (hval : (fun g => Additive.ofMul (sUnitsMaxRep.val S F (X g)) : ↥D × ↥D → Additive (AlgebraicClosure ℚ)ˣ) ∈
      levelCoboundaries₂ D.subtype (Rep.res D.subtype (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) :
    X ∈ levelCoboundaries₂ D.subtype (Rep.res (Subgroup.inclusion hD) (sUnitsMaxRep S F)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_levelCoboundaries2_sUnitsMaxRep_of_zsmul_mem_of_val_mem.solution

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_JZeroNeronAtPDataOrdV22
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_neronGlue
import Theorems.Thm_NeronModelInfra_neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_nonempty_neronExtension
attribute [-instance] NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp instTopologicallyFGOfFiniteType ValuationSubring.instIsAlgClosedResidueField
attribute [-simp] ModularCurve.coordOf_apply ModularCurve.coordOfEquiv_apply ModularCurve.diffChar_coe_apply ModularCurve.gramRangeBasisOf_coe ModularCurve.gramMatrixOf_apply RegularLocalRingQuotientAscent.dualNumberFst_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    Nonempty O.NeronExtension := by
  obtain ⟨Nfull, gN, LN, hcomm, ⟨hsm, hsep, hlft, hqc⟩, hext, openImm, specN, hoi, hmul, hsurj, hspmul, hspsurj, hsp0, hcomp⟩ :=
    ModularCurve.JZeroNeronObjectAtP.exists_neronGlue N₀ p hpN₀ A hA Λ hΛ O
  haveI := hsm; haveI := hsep; haveI := hlft; haveI := hqc
  have hpp : p.Prime := Fact.out
  haveI : IsDiscreteValuationRing ↥(shRing A) :=
    (ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA).1
  haveI : HenselianLocalRing ↥(shRing A) :=
    ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) A
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime p A hA
  obtain ⟨-, -, -, -, -, -, -, hacl⟩ :=
    ModularCurve.inertiaField_comap_incl_and_surjective_and_isAlgClosed_residueField p A hA
      (IsLocalRing.residue ↥A) IsLocalRing.residue_surjective
  haveI := hacl
  exact ⟨{ Nfull := Nfull, gN := gN, LN := LN, commN := hcomm,
           hN := by
             intro _
             exact NeronModelInfra.neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian
               ↥(invField A) gN LN hext,
           openImm := openImm, openImm_isOpenImmersion := hoi, openImm_mul := hmul,
           openImm_pts_surjective := hsurj, specN := specN, specN_mul := hspmul, specN_surjective := hspsurj,
           specN_eq_zero_iff := hsp0, comp_eq_specN := hcomp }⟩

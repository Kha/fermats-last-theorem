import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme

open scoped TensorProduct

open ModularCurve.DRLevel

noncomputable section
set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.DRModelPackageLevel.pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (toκ : ↥(GaloisRep.ratLocalizedAt q) →+* ResidueField ↥A)
    (Ms : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀))
    (es : Ms.C ⟶ pullback (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom toκ))) [IsIso es]
    (hes : es ≫ pullback.snd (igusaTo N₀ q) _ = Ms.toBase)
    (fm : FibreModel N₀ A q (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hfin : ∀ b : chartAlgFin N₀ q,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N₀)) ∈ fm.BFin)
    (hspFin : ∀ (y : {q' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q' ≫ Ms.toBase = 𝟙 _})
        (β : ↥(chartAlgFin N₀ q) →+* ResidueField ↥A),
        y.1 ≫ es ≫ pullback.fst (igusaTo N₀ q) _ =
          Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.IgusaScheme.ιFin N₀ q →
        ∀ b : ↥(chartAlgFin N₀ q),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) ∈
            (Ms.pointEquivPlace y).toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N₀) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) (β b) ∈
            (Ms.pointEquivPlace y).toValuationSubring.nonunits)
    (hCF : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀) :
    ∀ y' : {q' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔓.Mfib (ResidueField ↥A) toκ).C //
        q' ≫ (𝔓.Mfib (ResidueField ↥A) toκ).toBase = 𝟙 _},
      Ms.pointEquivPlace ⟨y'.1 ≫ 𝔓.efib (ResidueField ↥A) toκ ≫ inv es, by
          haveI := 𝔓.efib_iso (ResidueField ↥A) toκ
          rw [Category.assoc, Category.assoc, ← hes, IsIso.inv_hom_id_assoc, 𝔓.hefib]
          exact y'.2⟩ =
        AlgebraicCurve.Place.congrRingEquiv
          (e := (IntermediateField.equivOfEq hCF).toRingEquiv)
          (he := fun a => (IntermediateField.equivOfEq hCF).commutes a)
          ((𝔓.Mfib (ResidueField ↥A) toκ).pointEquivPlace y') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_efib_inv_eq_congrRingEquiv_pointEquivPlace_of_finChart_centrePin.solution

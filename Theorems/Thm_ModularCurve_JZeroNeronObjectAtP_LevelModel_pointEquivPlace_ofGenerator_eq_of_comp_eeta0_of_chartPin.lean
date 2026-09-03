import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_ModularCurve_FibreModel
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] HahnSeries.ramScale_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.IgusaScheme
  ModularCurve.JZeroNeronObjectAtP ModularCurve.CharPModel
open scoped TensorProduct

set_option maxHeartbeats 400000 in

theorem ModularCurve.JZeroNeronObjectAtP.LevelModel.pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ q A)
    (htrans : Transcendental (AlgebraicClosure ℚ) (CharPModel.jBar N₀))
    [hne : Fact (CharPModel.jBar N₀ ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀)))
      (modularFunctionFieldBar N₀)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(CharPModel.jBar N₀)⁻¹} : Set (modularFunctionFieldBar N₀)))
      (modularFunctionFieldBar N₀)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgFin N₀ q)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀))))
    (hFin : ∀ b : chartAlgFin N₀ q, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀)))) : modularFunctionFieldBar N₀)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ : modularFunctionFieldBar N₀)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans
    ∀ (eη : Mη.C ⟶ pullback (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ))))) (_ : IsIso eη)
      (heη : eη ≫ pullback.snd (igusaTo N₀ q) _ = Mη.toBase)
      (hchartFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ)
          (CharPModel.jBar N₀) ≫ eη ≫ pullback.fst (igusaTo N₀ q) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt q)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgFin N₀ q))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N₀ q)
      (x : {q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q' ≫ Mη.toBase = 𝟙 _})
      (x₀ : {q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q' ≫ M.Meta₀.toBase = 𝟙 _}),
      x.1 ≫ eη = x₀.1 ≫ M.eeta₀ →
      Mη.pointEquivPlace x = M.Meta₀.pointEquivPlace x₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin.solution

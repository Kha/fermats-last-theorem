import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
attribute [-simp] LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_scalar_mul_eq_localChar_centralChar_mul
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hbad : {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v}.Finite)
    (F : CubicInductionForm K pins ψ μ) (hF : F.form ≠ 0)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      F.whittakerLoc p (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) =
        ((NumberField.TateGlobal.localChar F.centralChar p t : ℂˣ) : ℂ) * F.whittakerLoc p h := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_scalar_mul_eq_localChar_centralChar_mul.solution

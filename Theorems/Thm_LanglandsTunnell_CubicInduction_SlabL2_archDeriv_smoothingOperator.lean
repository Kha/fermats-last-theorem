import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
attribute [-simp] LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open NumberField MeasureTheory IsDedekindDomain AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.glBorel in

theorem LanglandsTunnell.CubicInduction.SlabL2.archDeriv_smoothingOperator
    (φ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (hF : LocallyIntegrable F (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    IsSmoothingKernel (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0) ∧
      WhittakerBlock.archDeriv i j (smoothingOperator φ F) =
        smoothingOperator (fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0) F := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator.solution

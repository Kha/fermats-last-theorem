import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator
attribute [-simp] LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.injEq LanglandsTunnell.CubicInduction.AutomorphyDatum31.mk.sizeOf_spec LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.CubicInduction.SlabL2.casimir_smoothingOperator
    (φ H : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (hH : WhittakerBlock.IsArchSmooth3 H)
    (hreg : ∀ l : List (Fin 3 × Fin 3), Continuous (l.foldr (fun p G => WhittakerBlock.archDeriv p.1 p.2 G) H)) :
    WhittakerBlock.casimir1 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir1 H) ∧
      WhittakerBlock.casimir2 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir2 H) ∧
        WhittakerBlock.casimir3 (smoothingOperator φ H) = smoothingOperator φ (WhittakerBlock.casimir3 H) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_smoothingOperator.solution

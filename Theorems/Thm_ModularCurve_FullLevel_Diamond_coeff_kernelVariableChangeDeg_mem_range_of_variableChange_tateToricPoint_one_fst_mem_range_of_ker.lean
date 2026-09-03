import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker
    (M' : ℕ) [NeZero M']
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ ℓg)
    (hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / ℓg))
    (K'' : IntermediateField L (LaurentSeries L))
    (hK'' : K'' = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker))
    (p k : ℕ) [Fact p.Prime] (hpk : p ^ k ∣ M')
    (h : Polynomial (LaurentSeries L))
    (hh : ∀ (F' : Type) [Field F'] (f : L →+* F') (ζ : F'), IsPrimitiveRoot ζ (p ^ k) →
      h.map (ModularCurve.coeffMap f) =
        ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
          (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' 1 (ζ ^ a)).1))
    (C : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hx₁ : ((⟨(ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1, (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).2, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).1, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xP ∈ Set.range ((↑) : ↥K'' → LaurentSeries L))
    (hx₂ : ((⟨(ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).1, (ModularCurve.tateToricPoint L 1 (hζ.isUnit hℓg.ne_zero).unit).2, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).1, (ModularCurve.tateToricPoint L 1 ((hζ.isUnit hℓg.ne_zero).unit ^ 2)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C).xQ ∈ Set.range ((↑) : ↥K'' → LaurentSeries L)) :
    ∀ i : ℕ, (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h).coeff i ∈
      Set.range ((↑) : ↥K'' → LaurentSeries L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_coeff_kernelVariableChangeDeg_mem_range_of_variableChange_tateToricPoint_one_fst_mem_range_of_ker.solution

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ]
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (σ : (InfiniteAdeleRing ℚ)ˣ →* ℂˣ) (s : ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archZeta30 ν_mul (fun h => ∫ y : mixedEmbedding.mixedSpace ℚ,
        dualWhittakerFn3 W (h * lowerUnipotent21 ((InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm y) *
          (weylPrime3 * transposeInv3 g))) σ⁻¹ s 1 =
      archZetaDual31 ν_mul ν_add (fun h => W (h * g)) σ s 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_integral_dualWhittakerFn3_eq_archZetaDual31_of_eq_map_ringEquiv_mixedSpace.solution

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse

open scoped Classical in
open LanglandsTunnell LanglandsTunnell.CubicInduction in

theorem LanglandsTunnell.CubicInduction.archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (t : ℂ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v t e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (W : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (Φ : ℝ → ℂ)
    (hW : ∀ z : (InfiniteAdeleRing ℚ)ˣ,
      W (iotaGL (diagUnitGL2 z) * 1) = Φ (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)))
    (hΦ : MeasureTheory.AEStronglyMeasurable Φ MeasureTheory.volume) (s : ℂ) :
    0 < κ ∧
      archZeta30 ν_mul W (σ.comp E) s 1 =
        (κ : ℂ) * ∫ y : ℝ, Φ y * ArchR.quasiChar t (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt.solution

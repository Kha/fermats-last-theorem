import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.TateLocal.tateFourier_comp_mul_left (K : Type*) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (ψ : AddChar K ℂ) (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (f : K → ℂ) (a : K)
    (ha : a ≠ 0) (y : K) :
    tateFourier ψ μ (fun x => f (a * x)) y
      = ((modulus a : ℝ) : ℂ)⁻¹ * tateFourier ψ μ f (a⁻¹ * y) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_tateFourier_comp_mul_left.solution

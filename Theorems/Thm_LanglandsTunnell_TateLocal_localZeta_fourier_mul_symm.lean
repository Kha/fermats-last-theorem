import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm

set_option autoImplicit false

open MeasureTheory LanglandsTunnell.TateLocal
open scoped NNReal

theorem LanglandsTunnell.TateLocal.localZeta_fourier_mul_symm {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [MeasurableSingletonClass K] (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] [SFinite μ]
    [NullSingletonClass μ] (ψ : AddChar K ℂ) (f g : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ))
    (hswapL : Integrable (Function.uncurry fun y x : K =>
        g y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ f (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure μ).prod (mulMeasure μ)))
    (hswapR : Integrable (Function.uncurry fun y x : K =>
        f y * ((modulus y : ℝ) : ℂ) * tateFourier ψ μ g (y * x) *
          (charExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (1 - s)))
      ((mulMeasure μ).prod (mulMeasure μ)))
    (hker : ∀ x : K, x ≠ 0 → Integrable
        (fun p : K × K => f p.1 * g p.2 * (ψ (p.1 * p.2 * x) : ℂ)) (μ.prod μ)) :
    localZeta μ (tateFourier ψ μ f) χ⁻¹ (1 - s) * localZeta μ g χ s
      = localZeta μ (tateFourier ψ μ g) χ⁻¹ (1 - s) * localZeta μ f χ s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_localZeta_fourier_mul_symm.solution

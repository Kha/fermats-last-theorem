import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_localZeta30_localZetaDual31_twist_det

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.localZeta30_localZetaDual31_twist_det
    (v : HeightOneSpectrum (𝓞 ℚ))
    {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}
    (m : Measure (v.adicCompletion ℚ)ˣ) (m₁ : Measure (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) (χv η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) :
    (∀ s : ℂ, localZeta30 v m (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) η s g =
        ((χv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * localZeta30 v m W (η * χv) s g) ∧
    (∀ σ₀ : ℝ, IsLocalZeta30ConvergentAbove v m (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) η g σ₀ ↔
        IsLocalZeta30ConvergentAbove v m W (η * χv) g σ₀) ∧
    (∀ s : ℂ, localZetaDual31 v m m₁ (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) η s g =
        ((χv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * localZetaDual31 v m m₁ W (η * χv) s g) ∧
    (∀ σ₁ : ℝ,
      IsLocalZeta31ConvergentAbove v m m₁ (dualWhittakerFn3 (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ↔
        IsLocalZeta31ConvergentAbove v m m₁ (dualWhittakerFn3 W) (η * χv)⁻¹ (weylPrime3 * transposeInv3 g) σ₁) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_localZeta30_localZetaDual31_twist_det.solution

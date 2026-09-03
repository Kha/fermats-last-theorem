import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.integral_of_iotaGL_diagUnits2_ne_zero (v : HeightOneSpectrum (𝓞 ℚ))
    (ψv : AddChar (v.adicCompletion ℚ) ℂ)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψv x ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn ψv W)
    (hinv : ∀ (g : LocalGL3 v) (x y z : v.adicCompletion ℚ),
      x ∈ v.adicCompletionIntegers ℚ → y ∈ v.adicCompletionIntegers ℚ → z ∈ v.adicCompletionIntegers ℚ →
        W (g * upperUnipotent3 x y z) = W g)
    (t₁ t₂ : (v.adicCompletion ℚ)ˣ) (hW0 : W (iotaGL (diagUnits2 t₁ t₂)) ≠ 0) :
    (t₁ : v.adicCompletion ℚ) * (t₂ : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ ∧
      (t₂ : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integral_of_iotaGL_diagUnits2_ne_zero.solution

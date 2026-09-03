import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_CubicInductionForm_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (D : CubicInductionForm K pins ψ μ) (hD1 : D.dualWhittaker = dualWhittakerFn3 D.whittaker)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v, IsBadPlace K μ v → v ∈ T)
    (hg : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    D.dualWhittaker g =
      dualWhittakerFn3 D.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
        ∏ v ∈ T, dualWhittakerFn3 (D.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_CubicInductionForm_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod.solution

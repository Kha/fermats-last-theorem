import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hD1 : X.dualWhittaker = dualWhittakerFn3 X.whittaker)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v, IsBadPlace K μ v → v ∈ T)
    (hg : ∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) :
    X.dualWhittaker g =
      dualWhittakerFn3 X.whittakerArch (archComponent3 (𝓞 ℚ) ℚ g) *
        ∏ v ∈ T, dualWhittakerFn3 (X.whittakerLoc v) (componentAt3 (𝓞 ℚ) ℚ v g) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_dualWhittaker_eq_dualWhittakerFn3_whittakerArch_mul_prod_of_isCubicInductionDataOn.solution

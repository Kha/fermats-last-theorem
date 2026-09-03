import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm RSCarrier

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure finUnipotent) [μN.IsHaarMeasure]
    (W F : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hdet : ∀ g : finiteAdelicGL2Subgroup ℚ, W g * F g ≠ 0 →
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1)
    (hre : ∀ g : finiteAdelicGL2Subgroup ℚ, (W g * F g).im = 0 ∧ 0 ≤ (W g * F g).re)
    (hint : Integrable (fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
      (μ.withDensity (HaarQuotient.density finUnipotent μN)))
    (hpos : (μ.withDensity (HaarQuotient.density finUnipotent μN)) {g | W g * F g ≠ 0} ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, rsFinIntegral μ μN s W F = (c : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg.solution

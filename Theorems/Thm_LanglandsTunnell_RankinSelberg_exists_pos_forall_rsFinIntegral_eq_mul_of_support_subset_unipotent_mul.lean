import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_TateGlobalZeta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open NumberField.TateGlobal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (U : Subgroup (finiteAdelicGL2Subgroup ℚ))
    (hUc : IsCompact (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUo : IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)))
    (hUdet : ∀ u ∈ U, ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((u : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (s : ℂ) (W F : finiteAdelicGL2Subgroup ℚ → ℂ),
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
          W ((n : finiteAdelicGL2Subgroup ℚ) * g) * F ((n : finiteAdelicGL2Subgroup ℚ) * g) = W g * F g) →
        (∀ g : finiteAdelicGL2Subgroup ℚ, W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U ∧
            g = (n : finiteAdelicGL2Subgroup ℚ) * u) →
        (∀ u ∈ U, W u * F u = W 1 * F 1) →
        RSCarrier.rsFinIntegral μ μN s W F = (c : ℂ) * (W 1 * F 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_mul_of_support_subset_unipotent_mul.solution

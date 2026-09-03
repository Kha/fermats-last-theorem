import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import P2M.Util
namespace P2MW.S_AutomorphicForm_adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.AdelicVolume NumberField.TateGlobal

theorem solution
    (c u : ℝ) (hc : 0 < c) (t : AdelicGL2 (𝓞 ℚ) ℚ) (e₁ e₂ : ℝ) (he₁ : 0 < e₁) :
    adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
        (((· * t) '' integralWindowedSiegelSet ℚ c u) ∩
          {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) < ⊤ := by

  have hδ0 : 0 < ideleNorm ℚ (Matrix.GeneralLinearGroup.det t) := ideleNorm_pos _

  have hw : ∀ w : InfinitePlace ℚ, w = Rat.infinitePlace := fun w => Subsingleton.elim w _
  have hmult : ∀ w : InfinitePlace ℚ, w.mult = 1 := fun w => by
    rw [hw w]; exact InfinitePlace.mult_isReal ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

  have hsub : ((· * t) '' integralWindowedSiegelSet ℚ c u) ∩
        {g | ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ⊆
      (· * t) '' centreCutSiegelSet ℚ c u
        (e₁ / ideleNorm ℚ (Matrix.GeneralLinearGroup.det t)) (e₂ / ideleNorm ℚ (Matrix.GeneralLinearGroup.det t)) := by
    rintro y ⟨⟨g, hg, rfl⟩, hy⟩
    refine ⟨g, ?_, rfl⟩
    obtain ⟨hfin, hht, hwin⟩ := hg
    simp only [Set.mem_setOf_eq, map_mul, ideleNorm_mul, Set.mem_Icc] at hy

    have hN : ∀ w : InfinitePlace ℚ, archDetNorm w g = ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
      intro w
      rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ g hfin,
        Fintype.prod_subsingleton _ w, hmult w, pow_one]
    refine ⟨hfin, fun w => ?_, hwin, fun w => ?_⟩
    ·
      have : archHeight ℚ (glArch (𝓞 ℚ) ℚ g) = localHeight (archComponent ℚ w (glArch (𝓞 ℚ) ℚ g)) := by
        unfold archHeight
        rw [Fintype.prod_subsingleton _ w, hmult w, pow_one]
      rw [← this]; exact hht
    · rw [hN w, Set.mem_Icc]
      obtain ⟨h1, h2⟩ := hy
      exact ⟨(div_le_iff₀ hδ0).mpr h1, (le_div_iff₀ hδ0).mpr h2⟩
  exact (measure_mono hsub).trans_lt
    (adelicGLHaar_mul_right_centreCutSiegelSet_lt_top ℚ hc u (div_pos he₁ hδ0) _ t)

#print axioms solution

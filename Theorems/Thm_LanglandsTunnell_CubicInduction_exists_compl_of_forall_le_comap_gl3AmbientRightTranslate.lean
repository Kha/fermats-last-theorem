import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_compl_of_forall_le_comap_gl3AmbientRightTranslate
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (U : Submodule ℂ (LocalGL3 v → ℂ)) (hU : U ≤ principalSeries3 v χ)
    (hstab : ∀ g : LocalGL3 v, U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) g)) :
    ∃ U' : Submodule ℂ (LocalGL3 v → ℂ), U' ≤ principalSeries3 v χ ∧
      (∀ g : LocalGL3 v, U' ≤ U'.comap (gl3AmbientRightTranslate (R := ℂ) g)) ∧
      U ⊓ U' = ⊥ ∧ U ⊔ U' = principalSeries3 v χ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate.solution

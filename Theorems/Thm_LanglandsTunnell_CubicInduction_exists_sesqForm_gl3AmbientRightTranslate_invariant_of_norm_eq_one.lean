import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1) :
    ∃ B : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) →ₗ⋆[ℂ] ℂ,
      (∀ f f' : ↥(principalSeries3 v χ), B f f' = (starRingEnd ℂ) (B f' f)) ∧
      (∀ f : ↥(principalSeries3 v χ), f ≠ 0 → 0 < (B f f).re) ∧
      ∀ (g : LocalGL3 v) (f f' : ↥(principalSeries3 v χ)),
        B ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩
            ⟨gl3AmbientRightTranslate (R := ℂ) g f', rightTranslate_mem_principalSeries3 f'.2 g⟩ = B f f' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_sesqForm_gl3AmbientRightTranslate_invariant_of_norm_eq_one.solution

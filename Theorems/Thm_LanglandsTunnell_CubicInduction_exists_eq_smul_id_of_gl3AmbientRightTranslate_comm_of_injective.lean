import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hreg : Function.Injective χ)
    (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) :
    ∃ c : ℂ, T = c • LinearMap.id := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective.solution

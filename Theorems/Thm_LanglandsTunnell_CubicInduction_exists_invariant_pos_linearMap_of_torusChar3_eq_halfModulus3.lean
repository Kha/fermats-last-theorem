import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hδ : ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ, torusChar3 v χ a = halfModulus3 v a) :
    ∃ I : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ,
      (∀ (g : LocalGL3 v) (φ : ↥(principalSeries3 v χ)),
        I ⟨gl3AmbientRightTranslate (R := ℂ) g φ, rightTranslate_mem_principalSeries3 φ.2 g⟩ = I φ) ∧
      (∀ φ : ↥(principalSeries3 v χ), (∀ g : LocalGL3 v, ((φ : LocalGL3 v → ℂ) g).im = 0) → (I φ).im = 0) ∧
      ∀ φ : ↥(principalSeries3 v χ),
        (∀ g : LocalGL3 v, 0 ≤ ((φ : LocalGL3 v → ℂ) g).re ∧ ((φ : LocalGL3 v → ℂ) g).im = 0) →
          φ ≠ 0 → 0 < (I φ).re := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_invariant_pos_linearMap_of_torusChar3_eq_halfModulus3.solution

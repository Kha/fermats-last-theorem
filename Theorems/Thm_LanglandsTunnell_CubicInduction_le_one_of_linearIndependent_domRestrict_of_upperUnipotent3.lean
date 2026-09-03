import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem
    LanglandsTunnell.CubicInduction.le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Z : Fin 7 → Set (LocalGL3 v))
    (hZ : Z = ![∅,
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0},
      {g | cornerEntry v g * lowerMinor v g = 0},
      Set.univ])
    (W : Fin 7 → Submodule ℂ ↥(principalSeries3 v χ))
    (hW : ∀ k : Fin 7, W k = Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ Z k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)))
    (i : Fin 6) (n : ℕ)
    (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :
    (∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f) →
    (∀ j, ∀ f ∈ W i.succ, Λ j f = 0) →
    LinearIndependent ℂ (fun j => (Λ j).domRestrict (W i.castSucc)) →
    n ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3.solution

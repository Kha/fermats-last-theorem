import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
    (v : HeightOneSpectrum (𝓞 ℚ))
    (s : Finset (↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ)) :
    (∀ Λ ∈ s, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f) →
    (∀ Λ ∈ s, ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v (fun _ => 1))),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
        torusChar3 v (fun _ => 1) a * halfModulus3 v a * Λ f) →
    (LinearIndependent ℂ (fun Λ : ↥s => (Λ : ↥(principalSeries3 v (fun _ => 1)) →ₗ[ℂ] ℂ))) →
    s.card ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one.solution

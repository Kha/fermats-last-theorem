import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3
attribute [-simp] LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (θ : (Fin 3 → (v.adicCompletion ℚ)ˣ) → ℂ)
    (s : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :
    (∀ Λ ∈ s, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f) →
    (∀ Λ ∈ s, ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v χ)),
      Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ = θ a * Λ f) →
    (LinearIndependent ℂ (fun Λ : ↥s => (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))) →
    s.card ≤ {w : Equiv.Perm (Fin 3) |
      ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ, θ a = torusChar3 v (χ ∘ ⇑w) a * halfModulus3 v a}.ncard := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3.solution

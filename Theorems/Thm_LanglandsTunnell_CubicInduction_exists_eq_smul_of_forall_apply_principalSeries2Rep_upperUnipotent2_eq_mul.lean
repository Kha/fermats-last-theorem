import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (ψ : AddChar (p.adicCompletion ℚ) ℂ) (hψ : ψ ≠ 1)
    (ℓ₁ ℓ₂ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ)
    (hℓ₁ : ∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p χ)),
      ℓ₁ (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * ℓ₁ f)
    (hℓ₂ : ∀ (x : p.adicCompletion ℚ) (f : ↥(principalSeries2 p χ)),
      ℓ₂ (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * ℓ₂ f)
    (hne : ℓ₁ ≠ 0) :
    ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul.solution

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_IdeleProductMeasure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_MellinUniqueness_eq_smul_of_forall_isAdmissibleTwist_mellin_eq
attribute [-instance] instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open NumberField MeasureTheory
attribute [local instance] NumberField.Idele.ideleBorel in

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_smul_of_forall_isAdmissibleTwist_mellin_eq
    (F₁ F₂ G₁ G₂ : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (c : ℂ) (σ₁ σ₂ : ℝ)
    (_hF₁ : Measurable F₁) (_hF₂ : Measurable F₂)
    (_hi₁ : ∀ σ : ℝ, σ₁ ≤ σ → Integrable
      (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖F₁ x‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1)) (Idele.idelicHaar ℚ))
    (_hi₂ : ∀ σ : ℝ, σ ≤ σ₂ → Integrable
      (fun x : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖F₂ x‖ * (TateGlobal.ideleNorm ℚ x : ℝ) ^ (σ - 1)) (Idele.idelicHaar ℚ))
    (_hfe : ∀ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ →
      ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧ ∃ τ₁ τ₂ : ℝ,
        (∀ s : ℂ, τ₁ < s.re → E s = ∫ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            F₁ x * ((χ x : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ x : ℝ) : ℂ) ^ (s - 1) ∂(Idele.idelicHaar ℚ)) ∧
        (∀ s : ℂ, s.re < τ₂ → E s = c * ∫ x : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            F₂ x * ((χ x : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ x : ℝ) : ℂ) ^ (s - 1) ∂(Idele.idelicHaar ℚ)))
    (_hG₁ : Continuous G₁) (_hG₂ : Continuous G₂)
    (_hp₁ : ∀ᵐ x ∂(Idele.idelicHaar ℚ), HasSum
      (fun q : ℚˣ => F₁ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q * x)) (G₁ x))
    (_hp₂ : ∀ᵐ x ∂(Idele.idelicHaar ℚ), HasSum
      (fun q : ℚˣ => F₂ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q * x)) (G₂ x)) :
    G₁ = c • G₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_MellinUniqueness_eq_smul_of_forall_isAdmissibleTwist_mellin_eq.solution

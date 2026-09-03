import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

theorem AutomorphicForm.integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
    {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [SecondCountableTopology G₂] [T2Space G₂]
    (θ₁ : G₁ →* G₁) (hθ₁ : Continuous θ₁) (θ₂ : G₂ →* G₂) (hθ₂ : Continuous θ₂) (δ₁ : G₁) (δ₂ : G₂)
    (μ : @Measure (G₁ × G₂) (borel (G₁ × G₂))) (hμ : @Measure.IsHaarMeasure (G₁ × G₂) _ _ (borel _) μ)
    (μ₁ : @Measure G₁ (borel G₁)) (hμ₁ : @Measure.IsHaarMeasure G₁ _ _ (borel G₁) μ₁)
    (μ₂ : @Measure G₂ (borel G₂)) (hμ₂ : @Measure.IsHaarMeasure G₂ _ _ (borel G₂) μ₂)
    (τ₁ : @Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁) (hτ₁i : @Measure.IsInvInvariant _ (borel _) _ τ₁)
    (τ₂ : @Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _))
    (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂) (hτ₂i : @Measure.IsInvInvariant _ (borel _) _ τ₂)
    (e : AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂ →
      AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂))
    (he : ∀ p, ((e p : AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) : G₁ × G₂) =
      ((p.1 : G₁), (p.2 : G₂))) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (f : G₁ × G₂ → ℂ), Continuous f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      ∀ (W₁ : G₁ → ℝ) (W₂ : G₂ → ℝ), Continuous W₁ → (∀ x, 0 ≤ W₁ x) → HasCompactSupport W₁ →
        Continuous W₂ → (∀ x, 0 ≤ W₂ x) → HasCompactSupport W₂ →
        (∀ (x₁ : G₁) (x₂ : G₂), f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : G₁) * x₁)) = 1 ∧
          @integral _ ℝ _ _ (borel _) τ₂ (fun t => W₂ ((t : G₂) * x₂)) = 1) →
        letI τ : @Measure (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) (borel _) :=
          @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) e
            (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)
        (∀ x : G₁ × G₂, f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ
              (fun t => W₁ (((t : G₁ × G₂) * x).1) * W₂ (((t : G₁ × G₂) * x).2)) = 1) ∧
        (∀ w : G₁ × G₂ → ℝ, (∀ x, 0 ≤ w x) → Measurable[borel (G₁ × G₂)] w → HasCompactSupport w →
          (∀ x : G₁ × G₂, f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ (fun t => w ((t : G₁ × G₂) * x)) = 1) →
          @integral _ ℂ _ _ (borel (G₁ × G₂)) μ (fun x => f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) * (w x : ℂ)) =
            ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel G₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel G₂) μ₂ (fun x₂ =>
              f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) * ((W₁ x₁ * W₂ x₂ : ℝ) : ℂ)))) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer.solution

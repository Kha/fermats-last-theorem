import Mathlib.MeasureTheory.Integral.Bochner.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] {n : ℕ} (δ : Fin (n + 1) → G)
    (twc : (Fin (n + 1) → G) → Fin (n + 1) → G)
    (htwc : ∀ x j, twc x j = (x j)⁻¹ * δ j * x (j + 1))
    (T : Subgroup (Fin (n + 1) → G)) (hT : ∀ t, t ∈ T ↔ ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j)
    (y₀ γ : G) (hγ : γ = y₀⁻¹ * (List.ofFn δ).prod * y₀)
    (Φ : (Fin (n + 1) → G) → ℂ) (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (f f₁ : G → ℂ)
    (hf : ∀ h, f h =
      ∫ c : Fin n → G, Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h)) ∂(Measure.pi fun _ => μ))
    (hf₁ : ∀ h, f₁ h =
      ∫ c : Fin n → G, (‖Φ (Fin.snoc c (((List.ofFn c).prod)⁻¹ * h))‖ : ℂ) ∂(Measure.pi fun _ => μ))
    [MeasurableSpace T] (τ' : Measure T)
    (hmeas : Measurable fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀)
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set G)))
    (hval : Measurable fun s : Subgroup.centralizer ({γ} : Set G) => (s : G))
    (hτ : Measure.map (fun t : T => y₀⁻¹ * (t : Fin (n + 1) → G) 0 * y₀) τ' =
      Measure.map (fun s : Subgroup.centralizer ({γ} : Set G) => (s : G)) τ)
    (huniqT : ∀ F : (Fin (n + 1) → G) → ℂ, Measurable F →
      (∀ (t : T) (x : Fin (n + 1) → G), F ((t : Fin (n + 1) → G) * x) = F x) →
      ∀ w w' : (Fin (n + 1) → G) → ℝ, (∀ x, 0 ≤ w x) → (∀ x, 0 ≤ w' x) →
        Measurable w → Measurable w' →
        (∀ x, F x ≠ 0 → ∫ t : T, w ((t : Fin (n + 1) → G) * x) ∂τ' = 1) →
        (∀ x, F x ≠ 0 → ∫ t : T, w' ((t : Fin (n + 1) → G) * x) ∂τ' = 1) →
        ∫ x, F x * (w x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
          ∫ x, F x * (w' x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ))
    (huniqG : ∀ F : G → ℂ, Measurable F →
      (∀ (s : Subgroup.centralizer ({γ} : Set G)) (h : G), F ((s : G) * h) = F h) →
      ∀ w w' : G → ℝ, (∀ h, 0 ≤ w h) → (∀ h, 0 ≤ w' h) → Measurable w → Measurable w' →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w ((s : G) * h) ∂τ = 1) →
        (∀ h, F h ≠ 0 → ∫ s : Subgroup.centralizer ({γ} : Set G), w' ((s : G) * h) ∂τ = 1) →
        ∫ h, F h * (w h : ℂ) ∂μ = ∫ h, F h * (w' h : ℂ) ∂μ)
    (W₀ : (Fin (n + 1) → G) → ℝ) (hW₀ : ∀ x, 0 ≤ W₀ x) (hW₀m : Measurable W₀)
    (hW₀1 : ∀ x, Φ (twc x) ≠ 0 → ∫ t : T, W₀ ((t : Fin (n + 1) → G) * x) ∂τ' = 1)
    (w₀ : G → ℝ) (hw₀ : ∀ h, 0 ≤ w₀ h) (hw₀m : Measurable w₀)
    (hw₀1 : ∀ h, f (h⁻¹ * γ * h) ≠ 0 →
      ∫ s : Subgroup.centralizer ({γ} : Set G), w₀ ((s : G) * h) ∂τ = 1)
    (hw₁ : ∃ w₁ : G → ℝ, (∀ h, 0 ≤ w₁ h) ∧ Measurable w₁ ∧ Integrable w₁ μ ∧
      ∀ h, f₁ (h⁻¹ * γ * h) ≠ 0 →
        ∫ s : Subgroup.centralizer ({γ} : Set G), w₁ ((s : G) * h) ∂τ = 1)
    (hβ : ∃ β : (Fin n → G) → ℝ, (∀ c, 0 ≤ β c) ∧ Measurable β ∧
      Integrable β (Measure.pi fun _ => μ) ∧ ∀ c h, Φ (Fin.snoc c h) ≠ 0 → β c = 1) :
    ∫ x, Φ (twc x) * (W₀ x : ℂ) ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫ h, f (h⁻¹ * γ * h) * (w₀ h : ℂ) ∂μ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_twistedConj_mul_eq_integral_conj_fibreIntegral_mul.solution

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates RSCarrier

theorem LanglandsTunnell.Converse.exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hHaar : RSCarrier.archMeasure.IsHaarMeasure)
      (μN : Measure realUnipotent) [μN.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (coef : Fin n → ℂ)
      (W F Wd Fd : Fin n → GL (Fin 2) ℝ → ℂ) (Γ Γd e ed : ℂ → ℂ) (ε : ℂ) (σ₀ : ℝ)
      (_hN : ∀ i, ∀ u ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ,
        W i (u * g) * F i (u * g) = W i g * F i g)
      (_hNd : ∀ i, ∀ u ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ,
        Wd i (u * g) * Fd i (u * g) = Wd i g * Fd i g)
      (_hK : ∀ i, ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
        ∀ g : GL (Fin 2) ℝ, W i (g * k) * F i (g * k) = W i g * F i g)
      (_hKd : ∀ i, ∀ k ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 →
        ∀ g : GL (Fin 2) ℝ, Wd i (g * k) * Fd i (g * k) = Wd i g * Fd i g)
      (_hmeas : ∀ i, Measurable (W i) ∧ Measurable (F i) ∧ Measurable (Wd i) ∧ Measurable (Fd i))
      (_hint : ∀ i (s : ℂ), σ₀ < s.re → Integrable
        (fun g : GL (Fin 2) ℝ =>
          (W i g * F i g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)))
      (_hintd : ∀ i (s : ℂ), σ₀ < s.re → Integrable
        (fun g : GL (Fin 2) ℝ =>
          (Wd i g * Fd i g) * (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.archMeasure.withDensity (HaarQuotient.density realUnipotent μN)))
      (_hvec : ∀ s : ℂ, σ₀ < s.re →
        ∑ i, coef i *
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((W i p * F i p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
          = e s * Γ s)
      (_hpair : ∀ s : ℂ, σ₀ < s.re →
        ∑ i, coef i *
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if h : a₁ ≠ 0 ∧ 0 < a₂ then
                let p : GL (Fin 2) ℝ := upperUnit a₁ 0 a₂ h.1 h.2.ne'
                ((Wd i p * Fd i p) * (((|(Matrix.GeneralLinearGroup.det p : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
          = ed s * Γd s)
      (_hfe : ∀ s : ℂ, ed s = ε * e (1 - s)),
      (∀ s : ℂ, σ₀ < s.re →
          ∑ i, coef i * rsArchIntegral RSCarrier.archMeasure μN s (W i) (F i) = (c : ℂ) * (e s * Γ s)) ∧
        (∀ s : ℂ, σ₀ < s.re →
          ∑ i, coef i * rsArchIntegral RSCarrier.archMeasure μN s (Wd i) (Fd i) =
            (c : ℂ) * (ed s * Γd s)) ∧
        (∀ s : ℂ, (c : ℂ) * ed s = ε * ((c : ℂ) * e (1 - s))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities.solution

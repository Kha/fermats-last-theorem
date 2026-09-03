import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay

set_option autoImplicit false

p2m_open "MeasureTheory~hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable"

theorem MeasureTheory.exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay
    (r d c : ℕ) (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ)))
    (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ x ∈ Λ, s x.1 = ∑ i, ω i * (x.2 i : ℝ)) :
    ∃ K : ℝ, ∀ (Λ' : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ' : Λ' ≤ Λ)
      (χ : Λ' →+ (Fin c → AddCircle (1 : ℝ))) (m : Fin c → ℤ) (θ₀ : Fin c → AddCircle (1 : ℝ))
      (Ψ : (Fin r → ℝ) → ℂ) (hΨc : Continuous Ψ) (hΨi : Integrable Ψ) (C : ℝ)
      (hΨd : ∀ x : Fin r → ℝ, ‖Ψ x‖ ≤ C * ∏ i, (1 + |x i|)⁻¹ ^ 2)
      (hΨhatd : ∀ ξ : Fin r → ℝ,
        ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ x‖ ≤
          C * ∏ i, (1 + |ξ i|)⁻¹ ^ 2)
      (x₀ : Fin r → ℝ) (n₀ : Fin d → ℤ),
    ∃ μ : C((Fin d → AddCircle (1 : ℝ)), ℂ) →L[ℂ] ℂ,
      ‖μ‖ ≤ K * C ∧
      (∀ (τ : Fin d → AddCircle (1 : ℝ)), ∀ ε > (0 : ℝ),
        ∃ U : Fin d → Set (AddCircle (1 : ℝ)), (∀ i, IsOpen (U i) ∧ τ i ∈ U i) ∧
          ∀ g : C((Fin d → AddCircle (1 : ℝ)), ℂ),
            (∀ θ, (∃ i, θ i ∉ U i) → g θ = 0) → (∀ θ, ‖g θ‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (n : Fin d → ℤ) (e : C((Fin d → AddCircle (1 : ℝ)), ℂ)),
        (∀ θ, e θ = ∏ i, fourier (n i) (θ i)) →
        HasSum (fun γ : Λ' => if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ = n
            then Ψ (x₀ + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) * ∏ j, fourier (m j) (θ₀ j + χ γ j) else 0) (μ e) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay.solution

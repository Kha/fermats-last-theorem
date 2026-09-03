import Definitions.Def_AutomorphicForm_WindingDatum
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_sum_tsum_ite_of_contDiff_of_periodic

set_option autoImplicit false

p2m_open "MeasureTheory~exists_summable_forall_norm_setIntegral_mul_cexp_le_prod_of_contDiff_of_periodic~hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable"

theorem AutomorphicForm.WindingDatum.exists_forall_coeff_eq_sum_tsum_ite_of_contDiff_of_periodic
    {r d c N : ℕ}
    (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ γ ∈ Λ, s γ.1 = ∑ i, ω i * (γ.2 i : ℝ))
    (χ : Λ →+ (Fin c → AddCircle (1 : ℝ)))
    (lift : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (hlift : ∀ (γ : (Fin r → ℝ) × (Fin d → ℤ)) (hγ : γ ∈ Λ) (j : Fin c),
      ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j)
    (sub : Fin N → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hsub : ∀ i, sub i ≤ Λ)
    (G : Fin N → (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hG : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i))
    (R : ℝ) (hR : 0 ≤ R) (hGsupp : ∀ i (p : (Fin r → ℝ) × (Fin c → ℝ)), (∃ k, R < |p.1 k|) → G i p = 0)
    (hGper : ∀ i (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), G i (p.1, p.2 + Pi.single j 1) = G i p)
    (x₀ : Fin N → Fin r → ℝ) (n₀ : Fin N → Fin d → ℤ) (θ₀ : Fin N → Fin c → ℝ) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum r d c, ∀ n : Fin d → ℤ,
      𝒜.coeff n = ∑ i : Fin N, ∑' γ : sub i,
        if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
          G i (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ)))
        else 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_sum_tsum_ite_of_contDiff_of_periodic.solution

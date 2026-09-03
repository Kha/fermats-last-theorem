import Definitions.Def_AutomorphicForm_WindingDatum
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable

set_option autoImplicit false

open MeasureTheory

theorem AutomorphicForm.WindingDatum.exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable
    {r d c A q : ℕ}
    (Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hΛ : DiscreteTopology Λ)
    (s : (Fin r → ℝ) →ₗ[ℝ] ℝ) (ω : Fin d → ℝ) (hω : ω ≠ 0)
    (hpf : ∀ γ ∈ Λ, s γ.1 = ∑ i, ω i * (γ.2 i : ℝ))
    (χ : Λ →+ (Fin c → AddCircle (1 : ℝ)))
    (lift : (Fin r → ℝ) × (Fin d → ℤ) → (Fin c → ℝ))
    (hlift : ∀ (γ : (Fin r → ℝ) × (Fin d → ℤ)) (hγ : γ ∈ Λ) (j : Fin c),
      ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j)

    (kC : Fin c → Fin r) (kR : Fin q → Fin r)

    (B : Fin A → (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (C : Fin A → Fin q → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (E : Fin A → Fin c → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hC : ∀ a k, ContDiff ℝ (⊤ : ℕ∞) (C a k))
    (hE : ∀ a j, ContDiff ℝ (⊤ : ℕ∞) (E a j))
    (hper : ∀ (a : Fin A) (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c),
      B a (p.1, p.2 + Pi.single j 1) = B a p ∧ (∀ k, C a k (p.1, p.2 + Pi.single j 1) = C a k p) ∧
        ∀ j', E a j' (p.1, p.2 + Pi.single j 1) = E a j' p)
    (S : Set (Fin r → ℝ)) (hS : IsCompact S)
    (hsupp : ∀ (a : Fin A) (p : (Fin r → ℝ) × (Fin c → ℝ)), p.1 ∉ S →
      B a p = 0 ∧ (∀ k, C a k p = 0) ∧ ∀ j, E a j p = 0)

    (sub : ℕ → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))) (hsub : ∀ i, sub i ≤ Λ)
    (shape : ℕ → Fin A) (lam : ℕ → ℂ) (hlam : Summable fun i => ‖lam i‖)
    (x₀ : ℕ → Fin r → ℝ) (n₀ : ℕ → Fin d → ℤ) (θ₀ : ℕ → Fin c → ℝ) :
    ∃ 𝒜 : AutomorphicForm.WindingDatum r d c, ∀ n : Fin d → ℤ,
      𝒜.coeff n = ∑' i : ℕ, lam i * ∑' γ : sub i,
        if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + n₀ i = n then
          B (shape i) (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) +
            ∑ k : Fin q, ((|1 - Real.exp ((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kR k))| : ℝ) : ℂ) * C (shape i) k (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) +
            ∑ j : Fin c, ((‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) j : ℝ) : ℂ))‖ ^ 2 *
                  Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (((θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ))) j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
              E (shape i) j (x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1, θ₀ i + lift (γ : (Fin r → ℝ) × (Fin d → ℤ)))
        else 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindingDatum_exists_forall_coeff_eq_tsum_mul_tsum_ite_kinkWindow_of_contDiff_of_periodic_of_summable.solution

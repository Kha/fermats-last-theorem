import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord
    (K : Type) [Field K] [NumberField K]
    (P₀ P₁ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (hP₀ : ContDiff ℝ (⊤ : ℕ∞) P₀)
    (hP₀_per : ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ)
      (k : Fin (nrComplexPlaces K) → ℤ), P₀ (x, θ + fun j => (k j : ℝ)) = P₀ (x, θ))
    (hP_mul : ∀ (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P₀ (x + x', θ + θ') = P₀ (x, θ) * P₁ (x', θ'))
    (hP₀_bdd : ∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
      ∃ R : ℝ, ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ),
        P₀ (x, θ) ∈ C → ∀ i, |x i| ≤ R)
    (Wa : mixedSpace K → ℂ) (hWa : ContDiff ℝ (⊤ : ℕ∞) Wa)
    (C₀ : Set (mixedSpace K)) (hC₀ : IsCompact C₀) (hC₀u : ∀ y ∈ C₀, IsUnit y)
    (hWa0 : ∀ y, Wa y ≠ 0 → y ∈ C₀)
    {c d : ℕ} (cs : Fin (nrComplexPlaces K) → Fin d) (ts : Fin c → Fin d)
    (t : Fin c → ℂ) (ht : ∀ j, t j ≠ 0)
    (ℓ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ)
    (x₀ : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ₀ : Fin (nrComplexPlaces K) → ℝ) (n₀ : Fin c → ℤ) :
    ∃ G : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      (∃ Rb : ℝ, 0 ≤ Rb ∧
        ∀ p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ), (∃ i, Rb < |p.1 i|) → G p = 0) ∧
      (∀ (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ)) (J : Fin d),
        G (p.1, p.2 + Pi.single J 1) = G p) ∧
      ∀ (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (k : Fin c → ℤ)
        (Θ : Fin d → ℝ),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (t j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖t j‖ ^ (-(k j)) →
        G (x₀ + x, Θ) = (∏ j, t j ^ (-(n₀ j + k j))) * Wa (P₀ (x₀, θ₀) * P₁ (x, θ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord.solution

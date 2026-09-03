import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord

set_option autoImplicit false

p2m_open "NumberField NumberField.InfinitePlace NumberField.mixedEmbedding~exists_contDiff_periodic_forall_apply_eq_prod_zpow_neg_mul_apply_mul_of_polarCoord"

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord
    (K : Type) [Field K] [NumberField K]
    (P₀ P₁ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (hP₀ : ContDiff ℝ (⊤ : ℕ∞) P₀)
    (hP₀_per : ∀ (x : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ : Fin (nrComplexPlaces K) → ℝ)
      (k : Fin (nrComplexPlaces K) → ℤ), P₀ (x, θ + fun j => (k j : ℝ)) = P₀ (x, θ))
    (hP_mul : ∀ (x x' : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P₀ (x + x', θ + θ') = P₀ (x, θ) * P₁ (x', θ'))
    (hP₀_bdd : ∀ C : Set (mixedSpace K), IsCompact C → (∀ y ∈ C, IsUnit y) →
      ∃ R : ℝ, ∀ (x : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ : Fin (nrComplexPlaces K) → ℝ),
        P₀ (x, θ) ∈ C → ∀ i, |x i| ≤ R)
    (C₀ : Set (mixedSpace K)) (hC₀ : IsCompact C₀) (hC₀u : ∀ y ∈ C₀, IsUnit y)
    {c d : ℕ} (cs : Fin (nrComplexPlaces K) → Fin d) (ts : Fin c → Fin d)
    (t : Fin c → ℂ) (ht : ∀ j, t j ≠ 0)
    (ℓ : (Fin (Fintype.card (InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ)
    (x₀ : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (n₀ : Fin c → ℤ)

    (ιw : InfinitePlace K → Fin (Fintype.card (InfinitePlace K)))
    (s : {w : InfinitePlace K // w.IsReal} → ℤˣ)
    (cw : {w : InfinitePlace K // w.IsComplex} → Fin d) (hcw : Function.Injective cw)

    {q : ℕ} (wR : Fin q ≃ {w : InfinitePlace K // w.IsReal})
    (kR : Fin q → Fin (Fintype.card (InfinitePlace K))) (hkR : ∀ k, kR k = ιw (wR k).1)
    (kC : Fin d → Fin (Fintype.card (InfinitePlace K)))
    (hkC : ∀ w : {w : InfinitePlace K // w.IsComplex}, kC (cw w) = ιw w.1)

    (WB : mixedSpace K → ℂ) (hWB : ContDiff ℝ (⊤ : ℕ∞) WB) (hWB0 : ∀ y, WB y ≠ 0 → y ∈ C₀)
    (WC : InfinitePlace K → mixedSpace K → ℂ) (hWC : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (WC w))
    (hWC0 : ∀ w y, WC w y ≠ 0 → y ∈ C₀)
    (WE : InfinitePlace K → mixedSpace K → ℂ) (hWE : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (WE w))
    (hWE0 : ∀ w y, WE w y ≠ 0 → y ∈ C₀) :
    ∃ (Bw : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ) (Cw : Fin q → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ) (Ew : Fin d → (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ) → ℂ),
      (ContDiff ℝ (⊤ : ℕ∞) Bw ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Cw k)) ∧ ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Ew j)) ∧
      (∀ (p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ)) (J : Fin d),
        Bw (p.1, p.2 + Pi.single J 1) = Bw p ∧ (∀ k, Cw k (p.1, p.2 + Pi.single J 1) = Cw k p) ∧
          ∀ j, Ew j (p.1, p.2 + Pi.single J 1) = Ew j p) ∧
      (∃ Rb : ℝ, 0 ≤ Rb ∧ ∀ p : (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin d → ℝ), (∃ i, Rb < |p.1 i|) →
        Bw p = 0 ∧ (∀ k, Cw k p = 0) ∧ ∀ j, Ew j p = 0) ∧
      ∀ (x : (Fin (Fintype.card (InfinitePlace K)) → ℝ)) (θ : Fin (nrComplexPlaces K) → ℝ) (k : Fin c → ℤ) (Θ : (Fin d → ℝ)),
        (∀ j, ((Θ (cs j) : ℝ) : AddCircle (1 : ℝ)) = ((θ j : ℝ) : AddCircle (1 : ℝ))) →
        (∀ j, ((Θ (ts j) : ℝ) : AddCircle (1 : ℝ)) =
          ((-(k j : ℝ) * (t j).arg / (2 * Real.pi) : ℝ) : AddCircle (1 : ℝ))) →
        Real.exp (ℓ x) = ∏ j, ‖t j‖ ^ (-(k j)) →
        Bw (x₀ + x, Θ) +
            ∑ k' : Fin q, ((|1 - Real.exp ((x₀ + x) (kR k'))| : ℝ) : ℂ) * Cw k' (x₀ + x, Θ) +
            ∑ j : Fin d, ((‖(1 : ℂ) - Complex.exp ((((x₀ + x) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ j : ℝ) : ℂ))‖ ^ 2 *
                Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ + x) (kC j) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ j : ℝ) : ℂ))‖ : ℝ) : ℂ) *
              Ew j (x₀ + x, Θ) =
          (∏ j, t j ^ (-(n₀ j + k j))) *
            (WB (P₀ (x₀, 0) * P₁ (x, θ)) +
              ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal),
                ((if hw : w.IsReal then
                    (if s ⟨w, hw⟩ = 1 then
                        Real.exp (-((x₀ + x) (ιw w))) * |1 - Real.exp ((x₀ + x) (ιw w))|
                      else 1 + Real.exp (-((x₀ + x) (ιw w))))
                  else 0 : ℝ) : ℂ) * WC w (P₀ (x₀, 0) * P₁ (x, θ)) +
              ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                ((if hw : w.IsComplex then
                    Real.exp (-((x₀ + x) (ιw w))) *
                      (‖(1 : ℂ) - Complex.exp ((((x₀ + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2 *
                          Real.log ‖(1 : ℂ) - Complex.exp ((((x₀ + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ -
                        (x₀ + x) (ιw w) / 2 *
                          ‖(1 : ℂ) - Complex.exp ((((x₀ + x) (ιw w) / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((Θ (cw ⟨w, hw⟩) : ℝ) : ℂ))‖ ^ 2)
                  else 0 : ℝ) : ℂ) * WE w (P₀ (x₀, 0) * P₁ (x, θ))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_kinkWindows_forall_add_sum_abs_one_sub_exp_mul_add_sum_norm_one_sub_cexp_sq_mul_log_mul_eq_prod_zpow_neg_mul_of_polarCoord.solution

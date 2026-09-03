import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_summable_forall_fourierMode_kinkWindow_productPoisson

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_summable_forall_fourierMode_kinkWindow_productPoisson
    {r c : ℕ} (kC : Fin c → Fin r) {ιR : Type} [Fintype ιR] (kR : ιR → Fin r)
    (B : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (C : ιR → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (E : Fin c → (Fin r → ℝ) × (Fin c → ℝ) → ℂ)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (hC : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (C i)) (hE : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (E j))
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c),
      B (p.1, p.2 + Pi.single j 1) = B p ∧ (∀ i, C i (p.1, p.2 + Pi.single j 1) = C i p) ∧
        ∀ j', E j' (p.1, p.2 + Pi.single j 1) = E j' p)
    (S : Set (Fin r → ℝ)) (hS : IsCompact S)
    (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), p.1 ∉ S → B p = 0 ∧ (∀ i, C i p = 0) ∧ ∀ j, E j p = 0) :
    let G : (Fin r → ℝ) × (Fin c → ℝ) → ℂ := fun p =>
      B p + ∑ i, ((|1 - Real.exp (p.1 (kR i))| : ℝ) : ℂ) * C i p +
        ∑ j, ((‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp ((p.1 (kC j) / 2 : ℝ) + 2 * Real.pi * Complex.I * (p.2 j : ℝ))‖ : ℝ) : ℂ) *
            E j p
    let Gm : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        G (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))
    ∃ Cm : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ Cm m) ∧ Summable Cm ∧
      (∀ m, Continuous (Gm m) ∧ Integrable (Gm m) ∧
        (∀ x : Fin r → ℝ, ‖Gm m x‖ ≤ Cm m * ∏ k, (1 + |x k|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Gm m x‖ ≤
            Cm m * ∏ k, (1 + |ξ k|)⁻¹ ^ 2)) ∧
      ∀ p : (Fin r → ℝ) × (Fin c → ℝ),
        HasSum (fun m : Fin c → ℤ => Gm m p.1 * Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * p.2 j : ℝ) : ℂ)))
          (G p) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_summable_forall_fourierMode_kinkWindow_productPoisson.solution

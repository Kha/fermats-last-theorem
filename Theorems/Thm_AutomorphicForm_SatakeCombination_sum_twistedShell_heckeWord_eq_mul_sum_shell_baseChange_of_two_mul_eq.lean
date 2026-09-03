import Mathlib
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq

set_option autoImplicit false

open AutomorphicForm.SatakeCombination (univWord)

theorem AutomorphicForm.SatakeCombination.sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq
    (q ℓ : ℕ) (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ)
    (Wq WQ : ℕ → ℕ → ℕ)
    (hq00 : Wq 0 0 = 1) (hq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hqroot : ∀ n : ℕ, Wq (n + 1) 0 = (q + 1) * Wq n 1)
    (hqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + q * Wq n (s + 2))
    (hQ00 : WQ 0 0 = 1) (hQ0s : ∀ s : ℕ, WQ 0 (s + 1) = 0)
    (hQroot : ∀ n : ℕ, WQ (n + 1) 0 = (q ^ ℓ + 1) * WQ n 1)
    (hQstep : ∀ n s : ℕ, WQ (n + 1) (s + 1) = WQ n s + q ^ ℓ * WQ n (s + 2))
    (k j : ℕ)
    (φ : ℤ → ℕ → ℂ)
    (hφ : ∀ (a : ℤ) (s : ℕ), φ a s = if 2 * a + s = (k : ℤ) + 2 * j then (WQ k s : ℂ) else 0)
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (univWord (ℓ - 1) k j).support,
        (univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0))
    (d : ℕ) (P : ℕ → ℂ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((q : ℂ) ^ ((ℓ - 1) * (i - 1)) * ∑ t ∈ Finset.range ℓ, (q : ℂ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)
    (ρ : ℕ) (hρ : k + 2 * j = 2 * ρ) :
    ∑ m ∈ Finset.Icc 1 (ρ + d),
        (ℓ : ℂ) * m * ((q : ℂ) ^ ℓ) ^ m * (1 - ((q : ℂ) ^ ℓ)⁻¹) *
          (φ ρ 0 * P m +
            ∑ i ∈ Finset.range (min d (m - 1) + 1),
              (P i - P (i + 1)) * φ ((ρ : ℤ) - ((m - i : ℕ) : ℤ)) (2 * (m - i))) =
      (ℓ : ℂ) *
        (f ((ℓ * ρ : ℕ) : ℤ) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (q : ℂ) ^ s * (1 - (q : ℂ)⁻¹) +
          ∑ i ∈ Finset.Icc 1 (ℓ * ρ),
            ((d + i : ℕ) : ℂ) * (q : ℂ) ^ (d + i) * (1 - (q : ℂ)⁻¹) * f (((ℓ * ρ : ℕ) : ℤ) - i) (2 * i)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq.solution

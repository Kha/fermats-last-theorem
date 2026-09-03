import Mathlib
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_lt

set_option autoImplicit false

open AutomorphicForm.SatakeCombination (univWord)

theorem AutomorphicForm.SatakeCombination.sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_lt
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
    (ρa ρb : ℕ) (hlt : ρa < ρb) (hρ : ρa + ρb = k + 2 * j) :
    ∑ m ∈ Finset.Icc 1 ρa,
        (ℓ : ℂ) * m * ((q : ℂ) ^ ℓ) ^ m * (1 - ((q : ℂ) ^ ℓ)⁻¹) *
          φ ((ρa : ℤ) - m) (ρb - ρa + 2 * m) =
      (ℓ : ℂ) *
        ∑ i ∈ Finset.Icc 1 (ℓ * ρa),
          (i : ℂ) * (q : ℂ) ^ i * (1 - (q : ℂ)⁻¹) * f (((ℓ * ρa : ℕ) : ℤ) - i) (ℓ * (ρb - ρa) + 2 * i) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_lt.solution

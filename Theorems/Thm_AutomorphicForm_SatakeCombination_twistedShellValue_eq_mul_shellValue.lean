import Mathlib
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SatakeCombination_twistedShellValue_eq_mul_shellValue

set_option autoImplicit false

theorem AutomorphicForm.SatakeCombination.twistedShellValue_eq_mul_shellValue
    (q ℓ : ℕ) (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ)
    (Wq : ℕ → ℕ → ℕ) (hWq00 : Wq 0 0 = 1) (hWq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hWqroot : ∀ n : ℕ, Wq (n + 1) 0 = (q + 1) * Wq n 1)
    (hWqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + q * Wq n (s + 2))
    (WQ : ℕ → ℕ → ℕ) (hWQ00 : WQ 0 0 = 1) (hWQ0s : ∀ s : ℕ, WQ 0 (s + 1) = 0)
    (hWQroot : ∀ n : ℕ, WQ (n + 1) 0 = (q ^ ℓ + 1) * WQ n 1)
    (hWQstep : ∀ n s : ℕ, WQ (n + 1) (s + 1) = WQ n s + q ^ ℓ * WQ n (s + 2))
    (k j : ℕ)
    (φ : ℤ → ℕ → ℂ)
    (hφ : ∀ (a : ℤ) (s : ℕ), φ a s = if 2 * a + s = (k : ℤ) + 2 * j then (WQ k s : ℂ) else 0)
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (AutomorphicForm.SatakeCombination.univWord (ℓ - 1) k j).support,
        (AutomorphicForm.SatakeCombination.univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0))
    (d : ℕ)
    (P : ℕ → ℂ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((q : ℂ) ^ ((ℓ - 1) * (i - 1)) * ∑ t ∈ Finset.range (ℓ), (q : ℂ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)
    (ra rb : ℤ) :
    (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          ∑ m ∈ Finset.Icc 1 (ra.toNat + d),
            (ℓ : ℂ) * m * ((q : ℂ) ^ (ℓ)) ^ m * (1 - ((q : ℂ) ^ (ℓ))⁻¹) *
              (φ ra 0 * P m +
                ∑ i ∈ Finset.range (min d (m - 1) + 1),
                  (P i - P (i + 1)) * φ (ra - ((m - i : ℕ) : ℤ)) (2 * (m - i)))
        else
          ∑ m ∈ Finset.Icc 1 (min ra rb).toNat,
            (ℓ : ℂ) * m * ((q : ℂ) ^ (ℓ)) ^ m * (1 - ((q : ℂ) ^ (ℓ))⁻¹) *
              φ (min ra rb - m) ((ra - rb).natAbs + 2 * m))
      else 0) =
      (ℓ : ℂ) * (if ra + rb = (k : ℤ) + 2 * j then
        (if ra = rb then
          f ((ℓ : ℤ) * ra) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (q : ℂ) ^ s * (1 - (q : ℂ)⁻¹) +
            ∑ i ∈ Finset.Icc 1 (ℓ * ra.toNat),
              ((d + i : ℕ) : ℂ) * (q : ℂ) ^ (d + i) * (1 - (q : ℂ)⁻¹) * f ((ℓ : ℤ) * ra - i) (2 * i)
        else
          ∑ i ∈ Finset.Icc 1 (ℓ * (min ra rb).toNat),
            (i : ℂ) * (q : ℂ) ^ i * (1 - (q : ℂ)⁻¹) *
              f ((ℓ : ℤ) * min ra rb - i) (ℓ * (ra - rb).natAbs + 2 * i))
      else 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SatakeCombination_twistedShellValue_eq_mul_shellValue.solution

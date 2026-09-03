import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_Ihara_prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow

open scoped MatrixGroups
theorem Ihara.prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow (a b : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card (SL(2, ZMod (2 ^ a * 3 ^ b)))) : ℓ = 2 ∨ ℓ = 3 := by p2m_exact_reverting @_root_.P2MW.S_Ihara_prime_dvd_card_SL2_ZMod_two_pow_mul_three_pow.solution

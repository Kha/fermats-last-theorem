import Mathlib
import P2M.Util
import P2M.Sol.S_cyclotomic_velu_powerSums
open WeierstrassCurve
theorem cyclotomic_velu_powerSums {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    (∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2 = -((p : F) ^ 2 - 1) / 24) ∧
    (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2
        = ((p : F) ^ 2 - 1) * ((p : F) ^ 2 + 11) / 1440) ∧
    (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3
        = -(((p : F) ^ 2 - 1) * (2 * (p : F) ^ 4 + 23 * (p : F) ^ 2 + 191)) / 120960) := by p2m_exact_reverting @_root_.P2MW.S_cyclotomic_velu_powerSums.solution

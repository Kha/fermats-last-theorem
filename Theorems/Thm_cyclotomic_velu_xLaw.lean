import Mathlib
import P2M.Util
import P2M.Sol.S_cyclotomic_velu_xLaw
open WeierstrassCurve
theorem cyclotomic_velu_xLaw {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (X : F) (hX : ∀ k ∈ Finset.Icc 1 (p / 2), X ≠ ζ ^ k / (1 - ζ ^ k) ^ 2) :
    X + ∑ k ∈ Finset.Icc 1 (p / 2),
        (ζ ^ k / (1 - ζ ^ k) ^ 2 * (1 + 6 * (ζ ^ k / (1 - ζ ^ k) ^ 2)) / (X - ζ ^ k / (1 - ζ ^ k) ^ 2)
          + (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 * (1 + 4 * (ζ ^ k / (1 - ζ ^ k) ^ 2))
              / (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
      - ((p : F) ^ 2 - 1) / 12
      = X ^ p / ∏ k ∈ Finset.Icc 1 (p / 2), (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_cyclotomic_velu_xLaw.solution

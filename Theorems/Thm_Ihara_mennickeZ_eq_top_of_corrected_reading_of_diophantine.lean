import Definitions.Def_IharaMennickeCarrier
import P2M.Util
import P2M.Sol.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine

set_option autoImplicit false
theorem Ihara.mennickeZ_eq_top_of_corrected_reading_of_diophantine
    (q m : ℕ) [NeZero q] (hmq : Nat.Coprime m q) (hq : 2 ≤ q)
    (hdvd : (q ^ 2 - 1) ∣ m)
    (hsupp : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ m → ℓ ∣ (q ^ 2 - 1))
    (hsol : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → IsCoprime a b → IsCoprime a (m : ℤ) →
      ∃ (r : ℕ) (y t : ℤ),
        (b + a * y) * (m : ℤ) * t = a * ((q : ℤ) ^ (2 * (r * (m / (q ^ 2 - 1)))) - 1) ∧
        IsCoprime t (m : ℤ)) :
    Ihara.mennickeZ q m hmq = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Ihara_mennickeZ_eq_top_of_corrected_reading_of_diophantine.solution

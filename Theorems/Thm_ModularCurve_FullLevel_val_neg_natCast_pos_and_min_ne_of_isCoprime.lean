import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_val_neg_natCast_pos_and_min_ne_of_isCoprime

set_option autoImplicit false

theorem ModularCurve.FullLevel.val_neg_natCast_pos_and_min_ne_of_isCoprime
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hq : 5 ≤ q) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (g : ℤ) (hg : IsCoprime g q) :
    0 < (-(q : ZMod (q * ℓ))).val ∧ (-(q : ZMod (q * ℓ))).val < q * ℓ ∧
    0 < (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val ∧
    (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val < q * ℓ ∧
    2 * (-(q : ZMod (q * ℓ))).val ≠ q * ℓ ∧
    2 * (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val ≠ q * ℓ ∧
    min (-(q : ZMod (q * ℓ))).val (q * ℓ - (-(q : ZMod (q * ℓ))).val) ≠
      min (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val
        (q * ℓ - (-(q : ZMod (q * ℓ)) - (g : ZMod (q * ℓ)) * (ℓ : ZMod (q * ℓ))).val) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_val_neg_natCast_pos_and_min_ne_of_isCoprime.solution

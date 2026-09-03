import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_exists_surjective_units_to_multiplicative_padic_family

set_option autoImplicit false
theorem ZMod.exists_surjective_units_to_multiplicative_padic_family (p : ℕ) [Fact p.Prime] :
    ∃ πΔ : (q : ℕ) → ((ZMod q)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (q - 1)))),
      ∀ q : ℕ, q.Prime → q ≠ p → Function.Surjective (πΔ q) := by p2m_exact_reverting @_root_.P2MW.S_ZMod_exists_surjective_units_to_multiplicative_padic_family.solution

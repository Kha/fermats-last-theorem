import Mathlib
import P2M.Util
import P2M.Sol.S_Localization_Away_isDomain_and_charZero_and_isUnit_and_exists_injective_of_charZero

set_option autoImplicit false

theorem Localization.Away.isDomain_and_charZero_and_isUnit_and_exists_injective_of_charZero
    (M : ℕ) [NeZero M] (k : Type) [Field k] [CharZero k] :
    IsDomain (Localization.Away ((M : ℕ) : ℤ)) ∧ CharZero (Localization.Away ((M : ℕ) : ℤ)) ∧
      IsUnit ((M : ℕ) : Localization.Away ((M : ℕ) : ℤ)) ∧
      ∃ sk : Localization.Away ((M : ℕ) : ℤ) →+* k, Function.Injective sk := by p2m_exact_reverting @_root_.P2MW.S_Localization_Away_isDomain_and_charZero_and_isUnit_and_exists_injective_of_charZero.solution

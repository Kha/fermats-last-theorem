import Mathlib
import P2M.Util
import P2M.Sol.S_IsNoetherianRing_exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one

set_option autoImplicit false

theorem IsNoetherianRing.exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one
    (B : Type) [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ e : B, IsIdempotentElem e ∧ e ∉ 𝔭 ∧
      ∀ x : Localization.Away e, IsIdempotentElem x → x = 0 ∨ x = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_exists_isIdempotentElem_notMem_and_forall_isIdempotentElem_away_eq_zero_or_eq_one.solution

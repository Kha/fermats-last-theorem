import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced

set_option autoImplicit false

theorem Ideal.radical_span_inf_radical_annihilator_eq_bot_of_isReduced
    {S : Type} [CommRing S] [IsReduced S] (a : S) :
    (Ideal.span {a}).radical ⊓ ((Ideal.span {a}).annihilator).radical = ⊥ ∧
      ∀ s : S, a * s ∈ ((Ideal.span {a}).annihilator).radical →
        s ∈ ((Ideal.span {a}).annihilator).radical := by p2m_exact_reverting @_root_.P2MW.S_Ideal_radical_span_inf_radical_annihilator_eq_bot_of_isReduced.solution

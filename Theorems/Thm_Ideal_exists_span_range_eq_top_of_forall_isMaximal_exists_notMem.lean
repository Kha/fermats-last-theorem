import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_span_range_eq_top_of_forall_isMaximal_exists_notMem

set_option autoImplicit false

theorem Ideal.exists_span_range_eq_top_of_forall_isMaximal_exists_notMem
    {B : Type} [CommRing B] (P : B → Prop)
    (h : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal → ∃ s : B, s ∉ 𝔪 ∧ P s) :
    ∃ (n : ℕ) (g : Fin n → B), Ideal.span (Set.range g) = ⊤ ∧ ∀ i : Fin n, P (g i) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_span_range_eq_top_of_forall_isMaximal_exists_notMem.solution

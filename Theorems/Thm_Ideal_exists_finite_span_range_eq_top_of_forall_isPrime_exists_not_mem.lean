import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem

set_option autoImplicit false

universe u

theorem Ideal.exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem
    {B : Type u} [CommRing B] (P : B → Prop)
    (hloc : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∃ f : B, f ∉ 𝔭 ∧ P f) :
    ∃ (ι : Type u) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧ ∀ i : ι, P (f i) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem.solution

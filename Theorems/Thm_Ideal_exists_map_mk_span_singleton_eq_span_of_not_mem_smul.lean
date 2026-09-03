import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul

set_option autoImplicit false

theorem Ideal.exists_map_mk_span_singleton_eq_span_of_not_mem_smul
    {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ} (g : Fin (n + 1) → R)
    (x : R) (hx : x ∈ Ideal.span (Set.range g))
    (hxm : x ∉ IsLocalRing.maximalIdeal R • Ideal.span (Set.range g)) :
    ∃ g' : Fin n → R ⧸ Ideal.span ({x} : Set R),
      (Ideal.span (Set.range g)).map (Ideal.Quotient.mk (Ideal.span ({x} : Set R))) = Ideal.span (Set.range g') := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_map_mk_span_singleton_eq_span_of_not_mem_smul.solution

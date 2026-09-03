import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_height_map_quotientMk_span_singleton_add_one

set_option autoImplicit false

universe u

theorem Ideal.height_map_quotientMk_span_singleton_add_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] {x : R} (hx : x ∈ p)
    (hxmin : ∀ q ∈ minimalPrimes R, q ≤ p → x ∉ q) :
    (p.map (Ideal.Quotient.mk (Ideal.span {x}))).height + 1 = p.height := by p2m_exact_reverting @_root_.P2MW.S_Ideal_height_map_quotientMk_span_singleton_add_one.solution

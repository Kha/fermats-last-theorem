import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_isReduced_quotient_span_singleton_of_separable_map

open Polynomial

theorem Polynomial.isReduced_quotient_span_singleton_of_separable_map
    {D : Type*} [CommRing D] [IsDomain D] {g : D[X]} (hg : g.Monic)
    (hsep : (g.map (algebraMap D (FractionRing D))).Separable) :
    IsReduced (D[X] ⧸ Ideal.span {g}) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_isReduced_quotient_span_singleton_of_separable_map.solution

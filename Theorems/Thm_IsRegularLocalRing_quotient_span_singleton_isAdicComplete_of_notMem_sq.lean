import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_quotient_span_singleton_isAdicComplete_of_notMem_sq
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.quotient_span_singleton_isAdicComplete_of_notMem_sq
    (R : Type) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [IsRegularRing R] [IsAdicComplete (maximalIdeal R) R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) (hx0 : x ≠ 0)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧ IsDomain (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R ∧
      IsAdicComplete (maximalIdeal (R ⧸ Ideal.span {x})) (R ⧸ Ideal.span {x}) ∧
      maximalIdeal (R ⧸ Ideal.span {x}) = (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_quotient_span_singleton_isAdicComplete_of_notMem_sq.solution

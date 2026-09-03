import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_exists_notMem_sq_charZero_quotient_span_singleton
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.exists_notMem_sq_charZero_quotient_span_singleton
    (R : Type) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [IsRegularRing R] [CharZero R] (hd : 2 ≤ ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ x ≠ 0 ∧ CharZero (R ⧸ Ideal.span {x}) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_exists_notMem_sq_charZero_quotient_span_singleton.solution

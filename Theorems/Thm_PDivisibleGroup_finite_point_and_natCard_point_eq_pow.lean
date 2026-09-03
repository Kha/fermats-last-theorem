import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_finite_point_and_natCard_point_eq_pow

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.finite_point_and_natCard_point_eq_pow
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra O L] (v : ℕ) :
    Finite (H.Point L v) ∧ Nat.card (H.Point L v) = p ^ (v * h) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_finite_point_and_natCard_point_eq_pow.solution

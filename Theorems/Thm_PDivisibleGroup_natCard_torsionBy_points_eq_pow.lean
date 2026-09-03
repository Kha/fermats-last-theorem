import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_natCard_torsionBy_points_eq_pow

set_option autoImplicit false

theorem PDivisibleGroup.natCard_torsionBy_points_eq_pow
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L] (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (G.Points L) ((p ^ n : ℕ) : ℤ)) = p ^ (n * h) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_natCard_torsionBy_points_eq_pow.solution

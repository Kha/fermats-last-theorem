import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_nsmul_eq_zero_iff_exists_pointsMkAdd_eq

set_option autoImplicit false

theorem PDivisibleGroup.nsmul_eq_zero_iff_exists_pointsMkAdd_eq
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (L : Type) [CommRing L] [Algebra R L] (n : ℕ) (z : G.Points L) :
    (p ^ n) • z = 0 ↔ ∃ x : G.Point L n, G.pointsMkAdd L n (Additive.ofMul x) = z := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_nsmul_eq_zero_iff_exists_pointsMkAdd_eq.solution

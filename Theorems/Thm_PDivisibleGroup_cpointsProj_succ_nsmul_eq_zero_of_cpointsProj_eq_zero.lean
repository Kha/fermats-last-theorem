import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero

set_option autoImplicit false

theorem PDivisibleGroup.cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [CommRing S] [Algebra R S] (g : G.CPoints S) {i : ℕ} (hi : 1 ≤ i)
    (hg : G.cpointsProj S i g = 0) :
    G.cpointsProj S (i + 1) (p • g) = 0 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero.solution

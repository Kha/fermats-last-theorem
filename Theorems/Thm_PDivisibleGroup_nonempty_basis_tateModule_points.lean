import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_nonempty_basis_tateModule_points

set_option autoImplicit false

theorem PDivisibleGroup.nonempty_basis_tateModule_points
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L] :
    Nonempty (Module.Basis (Fin h) ℤ_[p] (TateModule p (G.Points L))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_nonempty_basis_tateModule_points.solution

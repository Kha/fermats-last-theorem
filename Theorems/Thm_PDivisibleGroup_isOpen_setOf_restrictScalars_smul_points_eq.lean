import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq

set_option autoImplicit false

theorem PDivisibleGroup.isOpen_setOf_restrictScalars_smul_points_eq
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (K L : Type) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [Algebra.IsAlgebraic K L] (z : G.Points L) :
    IsOpen {σ : L ≃ₐ[K] L | σ.restrictScalars R • z = z} := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq.solution

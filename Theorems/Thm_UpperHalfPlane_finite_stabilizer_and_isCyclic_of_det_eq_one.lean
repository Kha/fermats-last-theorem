import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    Finite ↥(MulAction.stabilizer ↥Γ τ) ∧ IsCyclic ↥(MulAction.stabilizer ↥Γ τ) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one.solution

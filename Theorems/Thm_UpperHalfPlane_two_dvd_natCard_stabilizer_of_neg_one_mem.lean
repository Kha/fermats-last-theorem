import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    2 ∣ Nat.card ↥(MulAction.stabilizer ↥Γ τ) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem.solution

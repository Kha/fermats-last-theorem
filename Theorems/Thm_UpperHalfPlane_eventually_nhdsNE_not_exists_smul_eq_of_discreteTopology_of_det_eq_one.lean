import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem UpperHalfPlane.eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology ↥Γ]
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (τ τ' : UpperHalfPlane) :
    ∀ᶠ z in 𝓝[≠] τ, ¬ ∃ γ ∈ Γ, γ • τ' = z := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one.solution

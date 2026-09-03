import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_isUnitOf_smul_eq_of_smul_qmPeriodLattice_eq

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.exists_isUnitOf_smul_eq_of_smul_qmPeriodLattice_eq
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ) (τ τ' : UpperHalfPlane) (c : ℂ)
    (h : c • qmPeriodLattice ι Λ τ = qmPeriodLattice ι Λ τ') :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = ι u ∧
      0 < g.det.val ∧ g • τ = τ' ∧ c * UpperHalfPlane.denom g τ = 1 := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_isUnitOf_smul_eq_of_smul_qmPeriodLattice_eq.solution

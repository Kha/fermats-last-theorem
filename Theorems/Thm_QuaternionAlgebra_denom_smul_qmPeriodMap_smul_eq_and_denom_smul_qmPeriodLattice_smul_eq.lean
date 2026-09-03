import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (x : ℍ[ℚ, a, b]) (g : GL (Fin 2) ℝ) (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = ι x) (hdet : 0 < g.det.val)
    (τ : UpperHalfPlane) :
    (∀ y : ℍ[ℚ, a, b], UpperHalfPlane.denom g τ • qmPeriodMap ι (g • τ) y = qmPeriodMap ι τ (y * x)) ∧
      (∀ v : Fin 2 → ℂ, v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ) ↔
        ∃ y ∈ Λ, qmPeriodMap ι τ (y * x) = v) ∧
      ((∀ ⦃y z : ℍ[ℚ, a, b]⦄, y ∈ Λ → z ∈ Λ → y * z ∈ Λ) → IsUnitOf Λ x →
        UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ) = qmPeriodLattice ι Λ τ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq.solution

import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) :
    Function.Injective (qmPeriodMap ι τ) ∧
      (∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), qmPeriodLattice ι Λ τ = Submodule.span ℤ (Set.range e)) ∧
      DiscreteTopology (qmPeriodLattice ι Λ τ) ∧
      Submodule.span ℝ (qmPeriodLattice ι Λ τ : Set (Fin 2 → ℂ)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span.solution

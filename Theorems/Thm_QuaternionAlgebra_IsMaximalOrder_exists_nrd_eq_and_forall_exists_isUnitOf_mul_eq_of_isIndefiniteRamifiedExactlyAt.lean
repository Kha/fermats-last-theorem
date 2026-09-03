import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
attribute [-instance] CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    (∃ s ∈ Λ, nrd s = (r : ℚ)) ∧
    (∀ s s' : ℍ[ℚ, a, b], s ∈ Λ → s' ∈ Λ → nrd s = (r : ℚ) → nrd s' = (r : ℚ) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ u * s = s') := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt.solution

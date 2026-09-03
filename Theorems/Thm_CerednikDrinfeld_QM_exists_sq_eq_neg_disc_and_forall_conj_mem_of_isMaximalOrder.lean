import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
attribute [-instance] CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk

set_option autoImplicit false

open scoped Quaternion

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) :
    (∃ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]))) ∧
    (∀ μ : ↥Λ, (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])) →
      ∀ x : ↥Λ, ∃ y : ↥Λ, (μ : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) = star (x : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b])) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_sq_eq_neg_disc_and_forall_conj_mem_of_isMaximalOrder.solution

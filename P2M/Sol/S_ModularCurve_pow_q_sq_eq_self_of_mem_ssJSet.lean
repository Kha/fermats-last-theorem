module

public import Definitions.Def_ModularCurve_SupersingularModuli
import P2M.Sol.S_WeierstrassCurve_j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero
import P2M.Util
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

namespace P2MW.S_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet

open ModularCurve

set_option autoImplicit false

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) : a ^ (q ^ 2) = a := by
  have h := WeierstrassCurve.j_pow_q_sq_eq_j_of_forall_q_zsmul_eq_zero q (WeierstrassCurve.ofJ a)
    (fun P hP => (mem_ssJSet_iff.mp ha) (WeierstrassCurve.ofJ a) (WeierstrassCurve.ofJ_j a) P
      (by rwa [natCast_zsmul] at hP))
  rwa [WeierstrassCurve.ofJ_j] at h
end S_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
end P2MW

public section
open ModularCurve
theorem ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) : a ^ (q ^ 2) = a := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet.solution
end

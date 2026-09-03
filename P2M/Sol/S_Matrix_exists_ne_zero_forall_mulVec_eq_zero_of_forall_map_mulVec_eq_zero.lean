import Mathlib
import P2M.Util
namespace P2MW.S_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero

set_option autoImplicit false

set_option maxHeartbeats 1600000

namespace Ws23
namespace Descent

theorem main {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Type*} (A : J → Matrix ι ι k) (v : ι → K) (hv : v ≠ 0)
    (hAv : ∀ j, ((A j).map (algebraMap k K)).mulVec v = 0) :
    ∃ w : ι → k, w ≠ 0 ∧ ∀ j, (A j).mulVec w = 0 := by
  classical

  let b := Module.Free.chooseBasis k K

  obtain ⟨y₀, hy₀⟩ : ∃ y, v y ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hrepr : b.repr (v y₀) ≠ 0 := by
    intro h; exact hy₀ (b.repr.map_eq_zero_iff.1 h)
  obtain ⟨t, ht⟩ : ∃ t, b.repr (v y₀) t ≠ 0 := by
    by_contra h
    push Not at h
    exact hrepr (Finsupp.ext h)
  refine ⟨fun y => b.repr (v y) t, fun h => ht (by simpa using congrFun h y₀), fun j => ?_⟩

  funext x
  have hx := congrFun (hAv j) x
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hx ⊢

  have : b.repr (∑ y, (algebraMap k K) (A j x y) * v y) t = ∑ y, A j x y * b.repr (v y) t := by
    rw [map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [← this, hx, map_zero, Finsupp.zero_apply]

end Ws23.Descent

theorem solution
    {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Type*} (A : J → Matrix ι ι k) (v : ι → K) (hv : v ≠ 0)
    (hAv : ∀ j, ((A j).map (algebraMap k K)).mulVec v = 0) :
    ∃ w : ι → k, w ≠ 0 ∧ ∀ j, (A j).mulVec w = 0 :=
  Ws23.Descent.main A v hv hAv

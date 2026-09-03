import Mathlib
import P2M.Util
namespace P2MW.S_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

theorem solution
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    IsUltrametricDist v.Completion := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one fun n => ?_
  have h1 : ((n : WithAbs v) : v.Completion) = (n : v.Completion) :=
    map_natCast UniformSpace.Completion.coeRingHom n
  have h2 : (n : WithAbs v).ofAbs = (n : K) := map_natCast (WithAbs.equiv v) n
  rw [← h1, UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs, h2]
  exact hv.apply_natCast_le_one

#print axioms solution

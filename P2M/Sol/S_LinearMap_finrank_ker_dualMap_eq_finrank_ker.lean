import Mathlib
import P2M.Util
namespace P2MW.S_LinearMap_finrank_ker_dualMap_eq_finrank_ker

set_option autoImplicit false
open Module

theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f)
  have h2 := f.finrank_range_add_finrank_ker
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  omega

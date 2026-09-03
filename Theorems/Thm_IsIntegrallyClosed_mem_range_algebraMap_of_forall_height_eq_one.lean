import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
set_option autoImplicit false

theorem IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K)
    (hx : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ a s : R, s ∉ P ∧ x * algebraMap R K s = algebraMap R K a) :
    x ∈ Set.range (algebraMap R K) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one.solution

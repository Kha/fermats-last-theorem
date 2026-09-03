import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one_exists_valuationSubring_ne_top

set_option autoImplicit false

theorem IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one_exists_valuationSubring_ne_top
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (x : K)
    (hx : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ W : ValuationSubring L, W ≠ ⊤ ∧
        (∀ y : K, (∃ a s : R, s ∉ P ∧ y * algebraMap R K s = algebraMap R K a) → algebraMap K L y ∈ W) ∧
        algebraMap K L x ∈ W) :
    x ∈ Set.range (algebraMap R K) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one_exists_valuationSubring_ne_top.solution

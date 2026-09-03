import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero

set_option autoImplicit false

universe u

theorem WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (x y : K) (hxy : (W.map (algebraMap R K)).toAffine.Equation x y)
    (hψ : ((W.map (algebraMap R K)).preΨ n).eval x = 0) :
    x ∈ Set.range (algebraMap R K) ∧ y ∈ Set.range (algebraMap R K) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero.solution

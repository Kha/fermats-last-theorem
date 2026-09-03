import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsAdicComplete.mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R)) (w : Rˣ)
    {B : Type*} [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (β : B) (hβ : β ^ e = algebraMap R B w) :
    β ∈ Set.range (algebraMap R B) := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_mem_range_algebraMap_of_pow_eq_unit_of_forall_sub_mem_maximalIdeal.solution

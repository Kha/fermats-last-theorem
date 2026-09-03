import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K) {a : K} {α β : Ωˣ}
    (hα : algebraMap K Ω a = (α : Ω) ^ p) (hβ : algebraMap K Ω a = (β : Ω) ^ p)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    kummerCocycle α σ = kummerCocycle β σ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup.solution

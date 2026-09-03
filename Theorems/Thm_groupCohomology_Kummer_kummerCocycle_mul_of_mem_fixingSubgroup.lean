import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_kummerCocycle_mul_of_mem_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.kummerCocycle_mul_of_mem_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K) {a : K} {α : Ωˣ} (hα : algebraMap K Ω a = (α : Ω) ^ p)
    {σ τ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) (hτ : τ ∈ K.fixingSubgroup) :
    kummerCocycle α (σ * τ) = kummerCocycle α σ * kummerCocycle α τ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_kummerCocycle_mul_of_mem_fixingSubgroup.solution

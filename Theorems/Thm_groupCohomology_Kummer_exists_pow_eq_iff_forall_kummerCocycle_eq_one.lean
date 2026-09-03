import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.exists_pow_eq_iff_forall_kummerCocycle_eq_one
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] (K : IntermediateField k Ω)
    {p : ℕ} (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K)
    {a : Kˣ} {α : Ωˣ} (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔ ∀ σ : K.fixingSubgroup, kummerCocycle α (σ : Ω ≃ₐ[k] Ω) = 1 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one.solution

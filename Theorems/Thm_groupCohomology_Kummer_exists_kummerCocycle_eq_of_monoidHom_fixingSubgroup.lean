import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {p : ℕ} [NeZero p]
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K)
    (χ : K.fixingSubgroup →* Ωˣ) (hχp : ∀ σ, χ σ ^ p = 1)
    (hlc : ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
      ∀ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → χ τ = 1) :
    ∃ (a : Kˣ) (α : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p ∧
      ∀ σ : K.fixingSubgroup, χ σ = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup.solution

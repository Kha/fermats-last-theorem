import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_exists_pow_eq_iff_of_fixingSubgroup

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.exists_pow_eq_iff_of_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] (K : IntermediateField k Ω)
    {p : ℕ} {a : Kˣ} {α : Ωˣ} (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔
      ∃ ζ : Ωˣ, ζ ^ p = 1 ∧ ∀ σ : K.fixingSubgroup,
        (σ : Ω ≃ₐ[k] Ω) • ζ / ζ = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_exists_pow_eq_iff_of_fixingSubgroup.solution

import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_natCard_quotient_range_pow_eq_natCard_levelHom

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {p : ℕ} [NeZero p]
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K)
    (hroot : ∀ a : Kˣ, ∃ α : Ωˣ, algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    Nat.card (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)
      = Nat.card {χ : K.fixingSubgroup →* Ωˣ // (∀ σ, χ σ ^ p = 1) ∧
          ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
            ∀ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → χ τ = 1} := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_natCard_quotient_range_pow_eq_natCard_levelHom.solution

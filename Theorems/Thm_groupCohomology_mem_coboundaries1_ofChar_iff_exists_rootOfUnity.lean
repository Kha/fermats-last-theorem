import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_coboundaries1_ofChar_iff_exists_rootOfUnity

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
theorem groupCohomology.mem_coboundaries1_ofChar_iff_exists_rootOfUnity
    {K L : Type} [Field K] [Field L] [Algebra K L] {p : ℕ} [Fact p.Prime]
    (χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ) {ζ : Lˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val) (c : (L ≃ₐ[K] L) → ZMod p) :
    c ∈ coboundaries₁ (ofChar χ) ↔
      ∃ η : Lˣ, η ^ p = 1 ∧ ∀ g : L ≃ₐ[K] L, g • η / η = ζ ^ (c g).val := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_coboundaries1_ofChar_iff_exists_rootOfUnity.solution

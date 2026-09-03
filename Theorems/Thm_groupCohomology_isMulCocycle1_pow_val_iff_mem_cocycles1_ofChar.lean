import Mathlib
import Definitions.Def_DualSelmer_ExtConditions
import P2M.Util
import P2M.Sol.S_groupCohomology_isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology
theorem groupCohomology.isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar
    {K L : Type} [Field K] [Field L] [Algebra K L] {p : ℕ} [Fact p.Prime]
    (χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ) {ζ : Lˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val) (c : (L ≃ₐ[K] L) → ZMod p) :
    IsMulCocycle₁ (fun g => ζ ^ (c g).val) ↔ c ∈ cocycles₁ (ofChar χ) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isMulCocycle1_pow_val_iff_mem_cocycles1_ofChar.solution

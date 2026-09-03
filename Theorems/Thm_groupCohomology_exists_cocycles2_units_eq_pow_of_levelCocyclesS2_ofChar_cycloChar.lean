import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
      (ofChar (k := ZMod p) (cycloChar p)))
    (hf : f ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p)))
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] (e : F →ₐ[ℚ] AlgebraicClosure ℚ)
    (ζF : Fˣ) (hζF : e (ζF : F) = ζ)
    (hconst : ∀ g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ y : F, s (e y) = e y) → (∀ y : F, s' (e y) = e y) → f (g * s, g' * s') = f (g, g')) :
    ∃ b : (F ≃ₐ[ℚ] F) × (F ≃ₐ[ℚ] F) → Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ,
      (∀ (g h : F ≃ₐ[ℚ] F) (ĝ ĥ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ y : F, ĝ (e y) = e (g y)) → (∀ y : F, ĥ (e y) = e (h y)) →
          b (g, h) = Additive.ofMul (ζF ^ ((f (ĝ, ĥ) : ZMod p).val))) ∧
      b ∈ cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[ℚ] F) Fˣ) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_cocycles2_units_eq_pow_of_levelCocyclesS2_ofChar_cycloChar.solution

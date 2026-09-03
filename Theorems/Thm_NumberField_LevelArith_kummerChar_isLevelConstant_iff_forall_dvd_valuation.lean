import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.kummerChar_isLevelConstant_iff_forall_dvd_valuation
    (p : ℕ) [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S) (hζF : ζ ∈ F) (x : (↥F)ˣ) :
    (∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), F'.IsUnramifiedOutside S ∧
        ∀ σ : ↥F.fixingSubgroup, (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F'.fixingSubgroup → kummerChar p ζ hζ F x σ = 0) ↔
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F), w ∉ placesOverPrimes ↥F (S : Set Nat.Primes) →
        (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero x) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_kummerChar_isLevelConstant_iff_forall_dvd_valuation.solution

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.LevelArith.exists_placesAbove_inl_equiv_infinitePlace
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L) (S : Finset Nat.Primes) :
    ∃ e : placesAbove L S (Sum.inl ()) ≃ NumberField.InfinitePlace ↥(levelField K L hKL),
      ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inl ())),
        e ((orbitQuotientAction K L hnorm ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ⧸ (extArithLoc S (Sum.inl ())).range)).smul γ x) =
          levelGal K L hKL γ • e x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace.solution

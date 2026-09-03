import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow
import P2M.Util
namespace P2MW.S_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel

open scoped NNReal

open ExtCitation.LocalLevel IsLocalRing in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (n : ℕ) :
    (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.FiniteIndex ∧
      (IsLocalRing.maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.index
        = Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ n := by
  haveI : IsDiscreteValuationRing (Rw q Kw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Kw
  haveI : Finite (ResidueField (Rw q Kw)) := ExtCitation.LocalLevel.finite_residueField_Rw q Kw
  have hidx : (maximalIdeal (Rw q Kw) ^ n).toAddSubgroup.index = Nat.card (ResidueField (Rw q Kw)) ^ n := by
    rw [AddSubgroup.index_eq_card]
    exact IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow n
  refine ⟨⟨?_⟩, hidx⟩
  rw [hidx]
  exact pow_ne_zero _ (Nat.card_pos (α := ResidueField (Rw q Kw))).ne'

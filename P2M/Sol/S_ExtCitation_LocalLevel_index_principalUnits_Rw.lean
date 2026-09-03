import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Theorems.Thm_IsLocalRing_index_principalUnits_one
import Theorems.Thm_IsDiscreteValuationRing_relIndex_principalUnits_add
import P2M.Util
namespace P2MW.S_ExtCitation_LocalLevel_index_principalUnits_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel IsLocalRing

open scoped NNReal

open IsLocalRing ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] {k : ℕ} (hk : 1 ≤ k) :
    (principalUnits (Rw q Kw) k).FiniteIndex ∧
      (principalUnits (Rw q Kw) k).index
        = (Nat.card (IsLocalRing.ResidueField (Rw q Kw)) - 1) * Nat.card (IsLocalRing.ResidueField (Rw q Kw)) ^ (k - 1) := by
  haveI : IsDiscreteValuationRing (Rw q Kw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Kw
  haveI : Finite (ResidueField (Rw q Kw)) := ExtCitation.LocalLevel.finite_residueField_Rw q Kw
  haveI : Fintype (ResidueField (Rw q Kw)) := Fintype.ofFinite _
  have h1 : (principalUnits (Rw q Kw) 1).index = Nat.card (ResidueField (Rw q Kw)) - 1 := by
    rw [IsLocalRing.index_principalUnits_one, Nat.card_units]
  have hrel : (principalUnits (Rw q Kw) k).relIndex (principalUnits (Rw q Kw) 1)
      = Nat.card (ResidueField (Rw q Kw)) ^ (k - 1) := by
    have := IsDiscreteValuationRing.relIndex_principalUnits_add (R := Rw q Kw) le_rfl (k - 1)
    rwa [Nat.add_sub_cancel' hk] at this
  have hidx : (principalUnits (Rw q Kw) k).index
      = (Nat.card (ResidueField (Rw q Kw)) - 1) * Nat.card (ResidueField (Rw q Kw)) ^ (k - 1) := by
    rw [← Subgroup.relIndex_mul_index (principalUnits_antitone hk), hrel, h1, mul_comm]
  refine ⟨⟨?_⟩, hidx⟩
  rw [hidx]
  have hc : 1 < Nat.card (ResidueField (Rw q Kw)) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  exact mul_ne_zero (by omega) (pow_ne_zero _ (by omega))

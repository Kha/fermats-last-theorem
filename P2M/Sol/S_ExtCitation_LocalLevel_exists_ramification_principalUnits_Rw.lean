import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_isAdicComplete_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_IsDiscreteValuationRing_map_powMonoidHom_principalUnits
import Theorems.Thm_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits
import P2M.Util
namespace P2MW.S_ExtCitation_LocalLevel_exists_ramification_principalUnits_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel IsLocalRing

open scoped NNReal

open IsLocalRing ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧
      Ideal.span {((q : ℕ) : Rw q Kw)} = IsLocalRing.maximalIdeal (Rw q Kw) ^ e ∧
      Nat.card (IsLocalRing.ResidueField (Rw q Kw)) = q ^ f ∧
      e * f = Module.finrank ℚ_[q] Kw ∧
      (∀ k : ℕ, e < k → (principalUnits (Rw q Kw) k).map (powMonoidHom q) = principalUnits (Rw q Kw) (k + e)) ∧
      (∀ k : ℕ, e < k → ∀ ζ ∈ principalUnits (Rw q Kw) k, ζ ^ q = 1 → ζ = 1) := by
  haveI : IsDiscreteValuationRing (Rw q Kw) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q Kw
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Rw q Kw)) (Rw q Kw) := ExtCitation.LocalLevel.isAdicComplete_Rw q Kw
  obtain ⟨e, f, he, hf, hspan, hcard, hef⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q Kw
  refine ⟨e, f, he, hf, hspan, hcard, hef, fun k hk => ?_, fun k hk ζ hζ hζq => ?_⟩
  · exact IsDiscreteValuationRing.map_powMonoidHom_principalUnits (Fact.out : q.Prime) hspan hk
  · exact IsDiscreteValuationRing.eq_one_of_pow_eq_one_of_mem_principalUnits hspan hk hζ hζq

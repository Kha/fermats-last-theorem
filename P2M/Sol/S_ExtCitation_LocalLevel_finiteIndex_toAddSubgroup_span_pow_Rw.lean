import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_index_toAddSubgroup_maximalIdeal_pow_Rw
import P2M.Util
namespace P2MW.S_ExtCitation_LocalLevel_finiteIndex_toAddSubgroup_span_pow_Rw

set_option autoImplicit false
open ExtCitation.LocalLevel

open scoped NNReal

open ExtCitation.LocalLevel IsLocalRing in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (N : ℕ) :
    (Ideal.span {((q : ℕ) : Rw q Kw) ^ N}).toAddSubgroup.FiniteIndex := by
  obtain ⟨e, f, -, -, hspan, -, -⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q Kw
  have h : Ideal.span {((q : ℕ) : Rw q Kw) ^ N} = IsLocalRing.maximalIdeal (Rw q Kw) ^ (e * N) := by
    rw [← Ideal.span_singleton_pow, hspan, ← pow_mul]
  rw [h]
  exact (ExtCitation.LocalLevel.index_toAddSubgroup_maximalIdeal_pow_Rw q Kw (e * N)).1

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_finrank_le_of_forall_resw_pow_eq

open ExtCitation ExtCitation.LocalLevel
open scoped NNReal
theorem ExtCitation.LocalLevel.finrank_le_of_forall_resw_pow_eq (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    (hst : ∀ g : GG q, ∀ y : PadicAlgCl q, y ∈ Kw → g y ∈ Kw)
    (hI : ∀ w : GG q, (∀ x : OO q, ((w • x - x ^ 1 : OO q) : PadicAlgCl q) ∈ (padicIntegers q).nonunits) →
      ∀ y : PadicAlgCl q, y ∈ Kw → w y = y)
    (f : ℕ) (hf0 : 0 < f) (hf : ∀ x : Rw q Kw, resw q Kw x ^ (q ^ f) = resw q Kw x) :
    Module.finrank ℚ_[q] Kw ≤ f := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_finrank_le_of_forall_resw_pow_eq.solution

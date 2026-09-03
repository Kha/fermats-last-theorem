import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_norm_sum_smul_eq_of_linearIndependent_resw

open ExtCitation ExtCitation.LocalLevel
open scoped NNReal
theorem ExtCitation.LocalLevel.norm_sum_smul_eq_of_linearIndependent_resw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]
    {ι : Type} [Fintype ι] (y : ι → Rw q Kw) (hy : LinearIndependent (ZMod q) (fun i => resw q Kw (y i)))
    (c : ι → ℚ_[q]) (j : ι) (hj : ∀ i, ‖c i‖ ≤ ‖c j‖) :
    ‖((∑ i, c i • ((y i : Kw)) : Kw) : PadicAlgCl q)‖ = ‖c j‖ := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_norm_sum_smul_eq_of_linearIndependent_resw.solution

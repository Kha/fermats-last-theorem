import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_residue_trace_eq_trace_residue_of_finrank_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (z : R.integers) :
    ∃ h : ((Algebra.trace (IntermediateField.adjoin L ({(x : F)} : Set F)) F (z : F) :
        IntermediateField.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers,
      R.residue ⟨_, h⟩ =
        ((Algebra.trace (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({R.residue x} : Set Fbar)) Fbar (R.residue z) :
          IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) :
            Fbar) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq.solution

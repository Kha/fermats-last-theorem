import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.linearIndependent_of_linearIndependent_residue
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar)
    {ι : Type*} (v : ι → R.integers)
    (hv : LinearIndependent (IsLocalRing.ResidueField A) (fun i => R.residue (v i))) :
    LinearIndependent L (fun i => (v i : F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_linearIndependent_of_linearIndependent_residue.solution

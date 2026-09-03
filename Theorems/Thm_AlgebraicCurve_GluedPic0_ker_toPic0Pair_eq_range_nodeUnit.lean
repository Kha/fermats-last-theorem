import Definitions.Def_AlgebraicCurve_GluedPic0
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit

theorem AlgebraicCurve.GluedPic0.ker_toPic0Pair_eq_range_nodeUnit {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Finset (AlgebraicCurve.Place K F × AlgebraicCurve.Place K F))
    (hrat : ∀ s : ↥S,
      Function.Surjective (algebraMap K ((s : AlgebraicCurve.Place K F × AlgebraicCurve.Place K F).1.ResidueField)) ∧
        Function.Surjective (algebraMap K ((s : AlgebraicCurve.Place K F × AlgebraicCurve.Place K F).2.ResidueField))) :
    (AlgebraicCurve.GluedPic0.toPic0Pair S).ker = (AlgebraicCurve.GluedPic0.nodeUnit S).range := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_GluedPic0_ker_toPic0Pair_eq_range_nodeUnit.solution

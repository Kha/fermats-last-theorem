import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_GluedPic0_natCard_ker_toPic0Pair_inf_torsionBy

theorem AlgebraicCurve.GluedPic0.natCard_ker_toPic0Pair_inf_torsionBy {K F : Type*} [Field K]
    [IsAlgClosed K] [Field F] [Algebra K F] (hCB : ConstantsAreBase K F)
    (S : Finset (Place K F × Place K F))
    (hrat : ∀ s ∈ S,
      Function.Surjective (algebraMap K (s.1.ResidueField)) ∧
        Function.Surjective (algebraMap K (s.2.ResidueField)))
    (m : ℕ) (hm : (m : K) ≠ 0) :
    Nat.card ↥((toPic0Pair S).ker ⊓
        (Submodule.torsionBy ℤ (GluedPic0 K F S) (m : ℤ)).toAddSubgroup) = m ^ (S.card - 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_GluedPic0_natCard_ker_toPic0Pair_inf_torsionBy.solution

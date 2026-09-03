import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_regularProlongation_ratFunc

theorem ValuationSubring.exists_regularProlongation_ratFunc
    {L : Type*} [Field L] (A : ValuationSubring L) :
    ∃ R : AlgebraicCurve.RegularProlongation A (RatFunc L) (RatFunc (IsLocalRing.ResidueField A)),
      (∃ hX : (RatFunc.X : RatFunc L) ∈ R.integers,
        R.residue ⟨RatFunc.X, hX⟩ = RatFunc.X) ∧
      (∀ p : Polynomial A, ∃ hp : algebraMap (Polynomial L) (RatFunc L) (p.map A.subtype) ∈ R.integers,
        R.residue ⟨algebraMap (Polynomial L) (RatFunc L) (p.map A.subtype), hp⟩ =
          algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A))
            (p.map (IsLocalRing.residue A))) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_regularProlongation_ratFunc.solution

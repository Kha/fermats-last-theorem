import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat

set_option autoImplicit false

theorem ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥A)] :
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat.solution

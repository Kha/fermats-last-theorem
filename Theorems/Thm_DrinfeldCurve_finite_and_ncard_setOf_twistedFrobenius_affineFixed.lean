import Mathlib
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_finite_and_ncard_setOf_twistedFrobenius_affineFixed

set_option autoImplicit false

namespace DrinfeldCurve

theorem finite_and_ncard_setOf_twistedFrobenius_affineFixed
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [Algebra (GaloisField q 2) K] [IsAlgClosed K]
    (η : rootsOfUnity (q + 1) (GaloisField q 2)) :
    {p : K × K | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.1 ^ q ^ 2 = p.1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.2 ^ q ^ 2 = p.2}.Finite ∧
    (((η : (GaloisField q 2)ˣ) : GaloisField q 2) = -1 →
      {p : K × K | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.1 ^ q ^ 2 = p.1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.2 ^ q ^ 2 = p.2}.ncard = q ^ 3 - q) ∧
    (((η : (GaloisField q 2)ˣ) : GaloisField q 2) ≠ -1 →
      {p : K × K | p.1 * p.2 ^ q - p.1 ^ q * p.2 = 1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.1 ^ q ^ 2 = p.1 ∧
        algebraMap (GaloisField q 2) K ((η : (GaloisField q 2)ˣ) : GaloisField q 2) * p.2 ^ q ^ 2 = p.2} = ∅) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_finite_and_ncard_setOf_twistedFrobenius_affineFixed.solution

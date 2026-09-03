import Mathlib
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed

set_option autoImplicit false

namespace DrinfeldCurve

theorem ncard_setOf_ellTwistedFrobenius_affineFixed
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [Algebra (GaloisField q 2) K] [IsAlgClosed K]
    (l₁ l₂ d : GaloisField q 2) (h12 : l₁ ≠ l₂) (hl1 : l₁ ^ (q + 1) = 1) (hl2 : l₂ ^ (q + 1) = 1)
    (hd : d ^ q = -d) (hd0 : d ≠ 0) :
    ((l₁ = -1 ∨ l₂ = -1) →
      {u : K × K | u.1 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₁ * u.1 ∧
          u.2 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₂ * u.2 ∧
          u.1 ^ (q + 1) - u.2 ^ (q + 1) = algebraMap (GaloisField q 2) K d}.ncard = q + 1) ∧
    (¬ (l₁ = -1 ∨ l₂ = -1) →
      {u : K × K | u.1 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₁ * u.1 ∧
          u.2 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₂ * u.2 ∧
          u.1 ^ (q + 1) - u.2 ^ (q + 1) = algebraMap (GaloisField q 2) K d}.ncard = (q + 1) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed.solution

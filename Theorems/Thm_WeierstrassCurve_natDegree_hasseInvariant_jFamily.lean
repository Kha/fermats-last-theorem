import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natDegree_hasseInvariant_jFamily
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.natDegree_hasseInvariant_jFamily
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).natDegree = (q - 1) / 4 ∧
      (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))).coeff 0 = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natDegree_hasseInvariant_jFamily.solution

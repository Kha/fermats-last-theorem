import Definitions.Def_ModularCurve_PDPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod

open CongruenceSubgroup ModularCurve.Period in
theorem ModularCurve.PDPairing.pairZ_nondegenerate_mod (N : ℕ) [NeZero N] [IsFreeGroup ↥(Gamma 4)]
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x') ∧
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ y' : parabolicHoms ℤ (Gamma0 N) ℤ, y = (p : ℤ) • y') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PDPairing_pairZ_nondegenerate_mod.solution

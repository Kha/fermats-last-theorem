import Definitions.Def_ModularCurve_PDPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0

open CongruenceSubgroup ModularCurve.Period in
theorem ModularCurve.PDPairing.pairZFun_jDeg0_iDeg0 (N N' d : ℕ) [NeZero N] [NeZero N'] [NeZero d]
    [IsFreeGroup ↥(Gamma 4)] (hNN' : N ∣ N') (hdd : d ∣ N' / N)
    (x' : Additive ↥(Gamma0 N') →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ)
    (hx' : IsParabolicHom (Gamma0 N') x') (hy : IsParabolicHom (Gamma0 N) y) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.jDeg0 N N' d ℤ ℤ hNN' hdd x') y =
      ModularCurve.PDPairing.pairZFun N' x' (ModularCurve.PDPairing.iDeg0 N N' d ℤ ℤ hNN' hdd y) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.solution

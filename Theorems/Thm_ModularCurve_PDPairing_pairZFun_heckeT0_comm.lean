import Definitions.Def_ModularCurve_PDPairing
import P2M.Util
import P2M.Sol.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm

open CongruenceSubgroup ModularCurve.Period in
theorem ModularCurve.PDPairing.pairZFun_heckeT0_comm (N ℓ : ℕ) [NeZero N] [NeZero ℓ]
    [IsFreeGroup ↥(Gamma 4)] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) (hφ : IsParabolicHom (Gamma0 N) φ) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.heckeT0 N ℓ ℤ φ) ψ =
      ModularCurve.PDPairing.pairZFun N φ (ModularCurve.PDPairing.heckeT0 N ℓ ℤ ψ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm.solution

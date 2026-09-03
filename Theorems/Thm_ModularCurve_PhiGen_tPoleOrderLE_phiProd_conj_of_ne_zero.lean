import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) : TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ - 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_tPoleOrderLE_phiProd_conj_of_ne_zero.solution

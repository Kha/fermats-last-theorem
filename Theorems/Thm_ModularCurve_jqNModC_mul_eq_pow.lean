import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqNModC_mul_eq_pow

open ModularCurve
theorem ModularCurve.jqNModC_mul_eq_pow (K : Type*) [CommRing K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    jqNModC K (N * ℓ) = (jqNModC K N) ^ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqNModC_mul_eq_pow.solution

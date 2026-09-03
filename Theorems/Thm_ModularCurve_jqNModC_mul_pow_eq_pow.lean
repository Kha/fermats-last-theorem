import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqNModC_mul_pow_eq_pow

open ModularCurve
theorem ModularCurve.jqNModC_mul_pow_eq_pow (K : Type*) [CommRing K] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (k : ℕ) :
    jqNModC K (N * ℓ ^ k) = (jqNModC K N) ^ (ℓ ^ k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqNModC_mul_pow_eq_pow.solution

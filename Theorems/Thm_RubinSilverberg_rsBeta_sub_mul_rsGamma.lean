import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_rsBeta_sub_mul_rsGamma

open RubinSilverberg
theorem RubinSilverberg.rsBeta_sub_mul_rsGamma {K : Type*} [Field K] (u : K) (hu : u ≠ 0) (hf : u ^ 10 + 11 * u ^ 5 - 1 ≠ 0) : rsBeta u - u * rsGamma u = -(kleinT u * kleinH u) / (144 * u ^ 4 * (u ^ 10 + 11 * u ^ 5 - 1) ^ 4) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_rsBeta_sub_mul_rsGamma.solution

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_IsKleinDatum_kleinH_ne_zero

open RubinSilverberg
theorem RubinSilverberg.IsKleinDatum.kleinH_ne_zero {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : RubinSilverberg.IsKleinDatum a b u₀) (ha : a ≠ 0) : RubinSilverberg.kleinH u₀ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_IsKleinDatum_kleinH_ne_zero.solution

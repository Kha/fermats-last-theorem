import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_IsKleinDatum_kleinT_ne_zero

open RubinSilverberg
theorem RubinSilverberg.IsKleinDatum.kleinT_ne_zero {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (h : RubinSilverberg.IsKleinDatum a b u₀) (hb : b ≠ 0) : RubinSilverberg.kleinT u₀ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_IsKleinDatum_kleinT_ne_zero.solution

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_kleinCurve_Delta

open RubinSilverberg
theorem RubinSilverberg.kleinCurve_Delta {K : Type*} [Field K] [CharZero K] (u : K) : (kleinCurve u).Δ = -kleinV u ^ 5 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_kleinCurve_Delta.solution

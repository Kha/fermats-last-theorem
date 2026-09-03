import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_kleinY_sq

open RubinSilverberg
theorem RubinSilverberg.kleinY_sq {K : Type*} [Field K] [CharZero K] (u : K) : kleinY u ^ 2 = kleinX u ^ 3 + (-kleinH u / 48) * kleinX u + kleinT u / 864 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_kleinY_sq.solution

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
namespace P2MW.S_RubinSilverberg_kleinY_sq

open RubinSilverberg

theorem solution {K : Type*} [Field K] [CharZero K] (u : K) : kleinY u ^ 2 = kleinX u ^ 3 + (-kleinH u / 48) * kleinX u + kleinT u / 864 := by
  unfold kleinY kleinX kleinH kleinT; ring

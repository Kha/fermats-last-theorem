import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember

open RubinSilverberg
theorem RubinSilverberg.exists_variableChange_kleinCurve_eq_rsMember {K : Type*} [Field K] [CharZero K] {a b u₀ : K} (hd : IsKleinDatum a b u₀) (ha : a ≠ 0) (hb : b ≠ 0) (l t k : K) (hden : rsDen u₀ l t ≠ 0) (hk : k ^ 2 = -18 * (b / a) * kleinH u₀ / kleinT u₀) : ∃ C : WeierstrassCurve.VariableChange K, (↑C.u⁻¹ : K) = k * rsDen u₀ l t ^ 5 ∧ C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ C • kleinCurve (rsNum u₀ l t / rsDen u₀ l t) = rsMember a b u₀ l t := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_exists_variableChange_kleinCurve_eq_rsMember.solution

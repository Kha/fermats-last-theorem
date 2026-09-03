import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_rsMember_zero

open RubinSilverberg
theorem RubinSilverberg.rsMember_zero {K : Type*} [Field K] (a b u₀ l : K) (hH : kleinH u₀ ≠ 0) (hT : kleinT u₀ ≠ 0) : rsMember a b u₀ l 0 = ⟨0, 0, 0, a, b⟩ := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_rsMember_zero.solution

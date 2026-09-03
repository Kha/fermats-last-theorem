import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_kleinTHom_atomsU

open RubinSilverberg
theorem RubinSilverberg.kleinTHom_atomsU {K : Type*} [Field K] [CharZero K] (α β s n d : K) (h1 : α * β = -s) (h2 : 2 * α ^ 2 = -5 - s) (h3 : 2 * β ^ 2 = s - 5) (h4 : s ^ 2 = 5) : kleinTHom (-α * n + β * d) (β * n + α * d) = s ^ 30 * kleinTHom n d := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_kleinTHom_atomsU.solution

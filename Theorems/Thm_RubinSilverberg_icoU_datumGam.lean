import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_icoU_datumGam

open RubinSilverberg
theorem RubinSilverberg.icoU_datumGam {K : Type*} [Field K] [CharZero K] (α β s u : K) (h1 : α * β = -s) (h2 : 2 * α ^ 2 = -5 - s) (h3 : 2 * β ^ 2 = s - 5) (h4 : s ^ 2 = 5) : ((-α * u + β) ^ 15 - 171 * (-α * u + β) ^ 10 * (β * u + α) ^ 5 + 247 * (-α * u + β) ^ 5 * (β * u + α) ^ 10 + 57 * (β * u + α) ^ 15) * (-α * u + β) ^ 4 = s ^ 18 * (β * (57 * u ^ 15 - 247 * u ^ 10 - 171 * u ^ 5 - 1) + α * (u ^ 4 * (u ^ 15 - 171 * u ^ 10 + 247 * u ^ 5 + 57))) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_icoU_datumGam.solution

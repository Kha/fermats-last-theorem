import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_isIcoSymmetry_icoT

open RubinSilverberg
theorem RubinSilverberg.isIcoSymmetry_icoT {K : Type*} [Field K] [CharZero K] : IsIcoSymmetry (icoT : Matrix (Fin 2) (Fin 2) K) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_isIcoSymmetry_icoT.solution

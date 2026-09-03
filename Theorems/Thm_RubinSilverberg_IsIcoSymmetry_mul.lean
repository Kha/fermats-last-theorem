import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_IsIcoSymmetry_mul

open RubinSilverberg
theorem RubinSilverberg.IsIcoSymmetry.mul {K : Type*} [Field K] [CharZero K] {g h : Matrix (Fin 2) (Fin 2) K} (hg : IsIcoSymmetry g) (hh : IsIcoSymmetry h) : IsIcoSymmetry (g * h) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_IsIcoSymmetry_mul.solution

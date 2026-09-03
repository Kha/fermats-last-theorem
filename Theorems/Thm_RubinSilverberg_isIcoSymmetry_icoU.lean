import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import P2M.Util
import P2M.Sol.S_RubinSilverberg_isIcoSymmetry_icoU

open RubinSilverberg
theorem RubinSilverberg.isIcoSymmetry_icoU {K : Type*} [Field K] [CharZero K] (ζ : K) (hζ : IsPrimitiveRoot ζ 5) : IsIcoSymmetry (icoU ζ) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_isIcoSymmetry_icoU.solution

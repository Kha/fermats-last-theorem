import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_rsFamilyB_eq_aeval

open RubinSilverberg
theorem RubinSilverberg.rsFamilyB_eq_aeval {K F : Type*} [Field K] [Field F] [Algebra K F] (b u₀ l : K) (x : F) : rsFamilyB (algebraMap K F b) (algebraMap K F u₀) (algebraMap K F l) x = Polynomial.aeval x (Polynomial.C (b / kleinT u₀) * kleinTHom (Polynomial.C (rsBeta u₀ + l * u₀) * Polynomial.X + Polynomial.C u₀) (Polynomial.C (rsGamma u₀ + l) * Polynomial.X + 1)) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_rsFamilyB_eq_aeval.solution

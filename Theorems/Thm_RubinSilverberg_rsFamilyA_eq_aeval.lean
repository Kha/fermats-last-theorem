import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_rsFamilyA_eq_aeval

open RubinSilverberg
theorem RubinSilverberg.rsFamilyA_eq_aeval {K F : Type*} [Field K] [Field F] [Algebra K F] (a u₀ l : K) (x : F) : rsFamilyA (algebraMap K F a) (algebraMap K F u₀) (algebraMap K F l) x = Polynomial.aeval x (Polynomial.C (a / kleinH u₀) * kleinHHom (Polynomial.C (rsBeta u₀ + l * u₀) * Polynomial.X + Polynomial.C u₀) (Polynomial.C (rsGamma u₀ + l) * Polynomial.X + 1)) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_rsFamilyA_eq_aeval.solution

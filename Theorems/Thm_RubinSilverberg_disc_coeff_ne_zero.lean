import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
import P2M.Sol.S_RubinSilverberg_disc_coeff_ne_zero

open RubinSilverberg
theorem RubinSilverberg.disc_coeff_ne_zero {K F : Type*} [Field K] [Field F] [CharZero F] [Algebra K F] {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀) (hV : kleinVHom (rsBeta u₀ + algebraMap K F l * u₀) (rsGamma u₀ + algebraMap K F l) ≠ 0) {pa pb : Polynomial K} (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t) (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t) : 4 * pa.coeff 20 ^ 3 + 27 * pb.coeff 30 ^ 2 ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_disc_coeff_ne_zero.solution

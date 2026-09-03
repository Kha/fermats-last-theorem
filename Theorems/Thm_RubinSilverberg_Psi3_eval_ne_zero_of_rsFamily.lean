import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily

open RubinSilverberg
theorem RubinSilverberg.Psi3_eval_ne_zero_of_rsFamily {K F : Type*} [Field K] [Field F] [CharZero F] [IsAlgClosed F] [Algebra K F] {a b l : K} {u₀ : F} (ha : a ≠ 0) (hb : b ≠ 0) (hu₀ : IsKleinDatum (algebraMap K F a) (algebraMap K F b) u₀) {pa pb : Polynomial K} (hpa : ∀ t : F, rsFamilyA (algebraMap K F a) u₀ (algebraMap K F l) t = (pa.map (algebraMap K F)).eval t) (hpb : ∀ t : F, rsFamilyB (algebraMap K F b) u₀ (algebraMap K F l) t = (pb.map (algebraMap K F)).eval t) (g : Polynomial K) : ((⟨0, 0, 0, pa, pb⟩ : WeierstrassCurve (Polynomial K)).Ψ₃).eval g ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_Psi3_eval_ne_zero_of_rsFamily.solution

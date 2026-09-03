import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Eval.Defs
import P2M.Util
import P2M.Sol.S_RubinSilverberg_exists_polynomial_rsFamily

open RubinSilverberg
theorem RubinSilverberg.exists_polynomial_rsFamily (a b l : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (u₀ : AlgebraicClosure ℚ) (h : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) a) (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀) : ∃ pa pb : Polynomial ℚ, pa.natDegree ≤ 20 ∧ pb.natDegree ≤ 30 ∧ ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) a) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t ∧ rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) b) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) l) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_exists_polynomial_rsFamily.solution

import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import P2M.Util
import P2M.Sol.S_RubinSilverberg_not_dvd_num_eval_and

open RubinSilverberg
theorem RubinSilverberg.not_dvd_num_eval_and {a b l : ℤ} {u₀ : AlgebraicClosure ℚ} (h₀ : IsKleinDatum (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀) {p : ℕ} (hp : p.Prime) (hp30 : ¬ p ∣ 30) (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) (hpD : ¬ (p : ℤ) ∣ 4 * a ^ 3 + 27 * b ^ 2) {pa pb : Polynomial ℚ} (hpa' : ∀ t : AlgebraicClosure ℚ, rsFamilyA (algebraMap ℚ (AlgebraicClosure ℚ) (a : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pa.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) (hpb' : ∀ t : AlgebraicClosure ℚ, rsFamilyB (algebraMap ℚ (AlgebraicClosure ℚ) (b : ℚ)) u₀ (algebraMap ℚ (AlgebraicClosure ℚ) (l : ℚ)) t = (pb.map (algebraMap ℚ (AlgebraicClosure ℚ))).eval t) (t₀ : ℤ) : ¬ ((p : ℤ) ∣ (pa.eval (t₀ : ℚ)).num ∧ (p : ℤ) ∣ (pb.eval (t₀ : ℚ)).num) := by p2m_exact_reverting @_root_.P2MW.S_RubinSilverberg_not_dvd_num_eval_and.solution

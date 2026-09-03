import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent

open MvPowerSeries

universe u

theorem MvPolynomial.exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (C : Matrix (Fin d) (Fin d) 𝓞) (hC : IsNilpotent (C.map (algebraMap 𝓞 (ZMod p)))) :
    ∃ χ : Fin d → MvPolynomial (Fin d) 𝓞, (∀ i, MvPolynomial.constantCoeff (χ i) = 0) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ),
        (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞))
            ((MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞) +
              ∑ j, MvPowerSeries.C (C i j) * (MvPowerSeries.X j : MvPowerSeries (Fin d) 𝓞) ^ p)).coeff m -
          (MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ),
        (MvPolynomial.aeval (fun j => (MvPolynomial.X j : MvPolynomial (Fin d) 𝓞) +
            ∑ l, MvPolynomial.C (C j l) * MvPolynomial.X l ^ p) (χ i)).coeff m -
          (MvPolynomial.X i : MvPolynomial (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent.solution

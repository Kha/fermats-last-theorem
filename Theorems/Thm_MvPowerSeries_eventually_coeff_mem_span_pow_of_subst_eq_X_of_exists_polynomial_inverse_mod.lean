import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import P2M.Util
import P2M.Sol.S_MvPowerSeries_eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod
attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

open MvPowerSeries

universe u

theorem MvPowerSeries.eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ}
    (φ ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0) (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hJ : ∀ (i j : Fin d) (m : Fin d →₀ ℕ), 2 ≤ m.degree →
      ((m j : ℕ) : 𝓞) * (φ i).coeff m ∈ Ideal.span {(p : 𝓞)})
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hψφ : ∀ i, subst φ (ψ i) = X i) (hφψ : ∀ i, subst ψ (φ i) = X i)
    (χ : Fin d → MvPolynomial (Fin d) 𝓞) (hχ0 : ∀ i, MvPolynomial.constantCoeff (χ i) = 0)
    (hχ : ∀ (i : Fin d) (m : Fin d →₀ ℕ),
      (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) (φ i)).coeff m -
        (X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) :
    ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (ψ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N} := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_eventually_coeff_mem_span_pow_of_subst_eq_X_of_exists_polynomial_inverse_mod.solution

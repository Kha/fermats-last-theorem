import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import P2M.Util
namespace P2MW.S_NumberField_NormIndex_IsAdmissibleModulusOfDegree_of_dvd_degree

set_option autoImplicit false

open NumberField NumberField.NormIndex

universe u v

theorem solution
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [Algebra K L]
    {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) {𝔣 : Ideal (𝓞 K)}
    (h : IsAdmissibleModulusOfDegree K L n 𝔣) : IsAdmissibleModulusOfDegree K L m 𝔣 := by
  refine ⟨h.1, fun v hv => (pow_dvd_pow _ ?_).trans (h.2 v hv)⟩
  have hm : m ≠ 0 := by
    rintro rfl
    exact hn (zero_dvd_iff.mp hmn)
  have hfac : ∀ p, m.factorization p ≤ n.factorization p := fun p =>
    (Nat.factorization_le_iff_dvd hm hn).mpr hmn p
  unfold admissibleExpOfDegree
  calc 1 + ∑ p ∈ m.primeFactors,
          (m.factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal
      ≤ 1 + ∑ p ∈ m.primeFactors,
          (n.factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal :=
        Nat.add_le_add_left
          (Finset.sum_le_sum fun p _ => Nat.mul_le_mul_right _ (Nat.succ_le_succ (hfac p))) 1
    _ ≤ 1 + ∑ p ∈ n.primeFactors,
          (n.factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal :=
        Nat.add_le_add_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Nat.primeFactors_mono hmn hn)
            fun _ _ _ => Nat.zero_le _) 1

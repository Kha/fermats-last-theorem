import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_forall_clearedFE_sum_smul_of_forall_clearedFE_of_forall_rational

set_option autoImplicit false

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_clearedFE_sum_smul_of_forall_clearedFE_of_forall_rational
    (N : ℕ) (hN : 1 < N) (C : ℂ) (r : ℤ)
    {ι : Type} [Fintype ι] (κ : ι → ℂ) (A B : ι → ℂ → ℂ)

    (hj : ∀ j : ι, ∃ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 ∧ Qd ≠ 0 ∧
      (∀ s : ℂ, σ < s.re → A j s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σd < s.re → B j s * Qd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)))) :
    ∀ (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ), Q ≠ 0 → Qd ≠ 0 →
      (∀ s : ℂ, σ < s.re →
        (∑ j, κ j * A j s) * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))) →
      (∀ s : ℂ, σd < s.re →
        (∑ j, κ j * B j s) * Qd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) →
      ∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) * ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C C).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((r : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_forall_clearedFE_sum_smul_of_forall_clearedFE_of_forall_rational.solution

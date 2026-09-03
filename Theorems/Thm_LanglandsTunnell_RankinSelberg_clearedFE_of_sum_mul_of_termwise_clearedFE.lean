import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_clearedFE_of_sum_mul_of_termwise_clearedFE

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.clearedFE_of_sum_mul_of_termwise_clearedFE
    (N : ℕ) (hN : 1 < N)
    (ι κ : Type) [Fintype ι] [Fintype κ]
    (c cD ΓA ΓZ Γ : ℂ) (kD kA kZ k : ℤ) (hΓ : Γ = cD * ΓA * ΓZ) (hk : k = kD + kA + kZ)
    (Ψ Ψd : ℂ → ℂ) (A Ad Z Zd : ι → κ → ℂ → ℂ)
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ₂ σ₃ : ℝ) (hQ : Q ≠ 0) (hQd : Qd ≠ 0)
    (hrat : (∀ s : ℂ, σ₂ < s.re → Ψ s * Q.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((m : ℂ) * s) * P.eval ((N : ℂ) ^ (-s))))
    (hratd : (∀ s : ℂ, σ₃ < s.re → Ψd s * Qd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))))
    (hsum : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Ψ s = c * ∑ i, ∑ j, A i j s * Z i j s)
    (hsumd : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Ψd s = c * (cD * (N : ℂ) ^ ((kD : ℂ) * s) * ∑ i, ∑ j, Ad i j s * Zd i j s))
    (hA : ∀ (i : ι) (j : κ), ∃ (PA PAd QA QAd : Polynomial ℂ) (mA mAd : ℤ) (σA σAd : ℝ), QA ≠ 0 ∧ QAd ≠ 0 ∧
      (∀ s : ℂ, σA < s.re → A i j s * QA.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mA : ℂ) * s) * PA.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σAd < s.re → Ad i j s * QAd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mAd : ℂ) * s) * PAd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((mAd : ℂ) * s) * PAd.eval ((N : ℂ) ^ (-s))) *
            QA.eval ((N : ℂ) ^ s) =
          ((Polynomial.C ΓA).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((kA : ℂ) * s)) *
            ((N : ℂ) ^ ((mA : ℂ) * (-s)) * PA.eval ((N : ℂ) ^ s)) *
            QAd.eval ((N : ℂ) ^ (-s))))
    (hZ : ∀ (i : ι) (j : κ), ∃ (PZ PZd QZ QZd : Polynomial ℂ) (mZ mZd : ℤ) (σZ σZd : ℝ), QZ ≠ 0 ∧ QZd ≠ 0 ∧
      (∀ s : ℂ, σZ < s.re → Z i j s * QZ.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mZ : ℂ) * s) * PZ.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σZd < s.re → Zd i j s * QZd.eval ((N : ℂ) ^ (-s)) = (N : ℂ) ^ ((mZd : ℂ) * s) * PZd.eval ((N : ℂ) ^ (-s))) ∧
      (∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((mZd : ℂ) * s) * PZd.eval ((N : ℂ) ^ (-s))) *
            QZ.eval ((N : ℂ) ^ s) =
          ((Polynomial.C ΓZ).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((kZ : ℂ) * s)) *
            ((N : ℂ) ^ ((mZ : ℂ) * (-s)) * PZ.eval ((N : ℂ) ^ s)) *
            QZd.eval ((N : ℂ) ^ (-s)))) :
    ∀ s : ℂ,
        ((1 : Polynomial ℂ)).eval ((N : ℂ) ^ s) *
            ((N : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((N : ℂ) ^ (-s))) *
            Q.eval ((N : ℂ) ^ s) =
          ((Polynomial.C Γ).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((k : ℂ) * s)) *
            ((N : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((N : ℂ) ^ s)) *
            Qd.eval ((N : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_clearedFE_of_sum_mul_of_termwise_clearedFE.solution

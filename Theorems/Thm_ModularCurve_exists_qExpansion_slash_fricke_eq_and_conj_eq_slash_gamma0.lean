import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 (M : ℕ) [NeZero M]
    {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n =
        ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 1 1 : ℤ) : ZMod M) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion 1
            (((⇑f : UpperHalfPlane → ℂ) ∣[k] W) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n = ι (σ (a n)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.solution

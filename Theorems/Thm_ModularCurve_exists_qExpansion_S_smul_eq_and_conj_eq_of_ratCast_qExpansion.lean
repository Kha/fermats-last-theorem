import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion

open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion (N : ℕ) [NeZero N]
    (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion N
        ((fun τ : UpperHalfPlane => G (ModularGroup.S • τ)) * ModularForm.discriminant ^ m)).coeff n =
          ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), ((γ 0 1 : ℤ) : ZMod N) = 0 → ((γ 1 1 : ℤ) : ZMod N) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N
            ((fun τ : UpperHalfPlane => G (ModularGroup.S • γ • τ)) *
              ModularForm.discriminant ^ m)).coeff n = ι (σ (a n)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.solution

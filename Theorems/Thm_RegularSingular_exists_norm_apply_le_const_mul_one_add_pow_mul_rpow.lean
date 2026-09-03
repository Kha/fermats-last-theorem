import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import P2M.Util
import P2M.Sol.S_RegularSingular_exists_norm_apply_le_const_mul_one_add_pow_mul_rpow

set_option autoImplicit false

universe u v

theorem RegularSingular.exists_norm_apply_le_const_mul_one_add_pow_mul_rpow
    (D d : ℕ) (m τ θ : ℝ) (hθ : θ < τ) :
    ∃ e : ℕ, ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      (r : ℕ) (q : Polynomial ℂ), q ≠ 0 → q.natDegree ≤ D → ∀ i₀ : Fin r,
    ∃ κ₀ : ℝ, ∀ (L : ℝ), 0 ≤ L →
      ∀ (M : Matrix (Fin r) (Fin r) ℂ) (A : Fin d → ((Fin r → E) →L[ℂ] (Fin r → E))),
      (∀ i j, ‖M i j‖ ≤ L) → Polynomial.aeval M q = 0 → (∀ k, ‖A k‖ ≤ L) →
      ∀ (F F' : ℝ → (Fin r → E)) (B : ℝ),
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt F (F' y) y ∧
        (y : ℂ) • F' y = (fun i => ∑ j, M i j • F y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A k (F y)) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y‖ ≤ B * y ^ (-m)) →
      (∃ C : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y i₀‖ ≤ C * y ^ τ) →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y i₀‖ ≤ κ₀ * (1 + L) ^ e * B * y ^ θ := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_exists_norm_apply_le_const_mul_one_add_pow_mul_rpow.solution

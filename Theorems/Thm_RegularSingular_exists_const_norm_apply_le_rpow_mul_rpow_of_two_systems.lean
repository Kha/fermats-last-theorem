import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import P2M.Util
import P2M.Sol.S_RegularSingular_exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems

set_option autoImplicit false

universe u v

theorem RegularSingular.exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (r d d' : ℕ) (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0) (i₀ : Fin r) (L m m' τ θ : ℝ) (hθ : θ < τ) :
    ∃ κ : ℝ, ∀ (M M' : ℝ → Matrix (Fin r) (Fin r) ℂ) (A : ℝ → Fin d → ((Fin r → E) →L[ℂ] (Fin r → E)))
      (A' : ℝ → Fin d' → ((Fin r → E) →L[ℂ] (Fin r → E))),
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∀ i j, ‖M z i j‖ ≤ L) → (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ i j, ‖M' y i j‖ ≤ L) →
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∀ k, ‖A z k‖ ≤ L) → (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ k, ‖A' y k‖ ≤ L) →
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, Polynomial.aeval (M z) q = 0) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, Polynomial.aeval (M' y) q' = 0) →
      ∀ (F Fy Fz : ℝ → ℝ → (Fin r → E)) (B : ℝ),
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (fun y => F y z) (Fy y z) y ∧
        (y : ℂ) • Fy y z =
          (fun i => ∑ j, M z i j • F y z j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A z k (F y z)) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (fun z => F y z) (Fz y z) z ∧
        (z : ℂ) • Fz y z =
          (fun i => ∑ j, M' y i j • F y z j) + ∑ k : Fin d', ((z : ℂ) ^ ((k : ℕ) + 1)) • A' y k (F y z)) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖F y z‖ ≤ B * y ^ (-m) * z ^ (-m')) →
      (∀ z ∈ Set.Ioc (0 : ℝ) 1, ∃ C : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F y z i₀‖ ≤ C * y ^ τ) →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1, ∃ C : ℝ, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖F y z i₀‖ ≤ C * z ^ τ) →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖F y z i₀‖ ≤ κ * B * (y ^ θ * z ^ θ) := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_exists_const_norm_apply_le_rpow_mul_rpow_of_two_systems.solution

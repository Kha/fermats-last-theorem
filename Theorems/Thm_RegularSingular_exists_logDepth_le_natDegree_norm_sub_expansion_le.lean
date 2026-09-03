import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import P2M.Util
import P2M.Sol.S_RegularSingular_exists_logDepth_le_natDegree_norm_sub_expansion_le

set_option autoImplicit false

universe u v

theorem RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le (q : Polynomial ℂ) (hq : q ≠ 0) :
    ∃ D : ℕ, D ≤ q.natDegree ∧
      ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (r d : ℕ) (L m ρ θ : ℝ),
        (∀ e : ℂ, q.IsRoot e → ∀ n : ℕ, ρ < (e + n).re → θ < (e + n).re) →
    ∃ (S : Finset ℂ) (κ : ℝ),
      (∀ μ ∈ S, μ.re ≤ ρ ∧ ∃ (e : ℂ) (n : ℕ), q.IsRoot e ∧ μ = e + n) ∧
      ∀ (P : Type v) [TopologicalSpace P] (M : P → Matrix (Fin r) (Fin r) ℂ)
        (A : P → Fin d → ((Fin r → E) →L[ℂ] (Fin r → E))),
        Continuous M → (∀ p i j, ‖M p i j‖ ≤ L) → (∀ p, Polynomial.aeval (M p) q = 0) →
        (∀ k, Continuous fun p => A p k) → (∀ p k, ‖A p k‖ ≤ L) →
        ∀ (F F' : P → ℝ → (Fin r → E)) (B : P → ℝ),
        ContinuousOn (fun w : P × ℝ => F w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 1) →
        (∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀) →
        (∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (F p) (F' p y) y ∧
          (y : ℂ) • F' p y =
            (fun i => ∑ j, M p i j • F p y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A p k (F p y)) →
        (∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y‖ ≤ B p * y ^ (-m)) →
        ∃ c : ℂ → ℕ → P → (Fin r → E),
          (∀ μ j, Continuous (c μ j)) ∧
          ∀ p, (∀ μ j, ‖c μ j p‖ ≤ κ * B p) ∧ (∀ μ ∈ S, μ.re < -m → ∀ j, c μ j p = 0) ∧
            ∀ y ∈ Set.Ioc (0 : ℝ) 1,
              ‖F p y - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
                  ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c μ j p‖ ≤ κ * B p * y ^ θ := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_exists_logDepth_le_natDegree_norm_sub_expansion_le.solution

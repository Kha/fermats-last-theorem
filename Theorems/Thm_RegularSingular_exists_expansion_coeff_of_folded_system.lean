import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic
import P2M.Util
import P2M.Sol.S_RegularSingular_exists_expansion_coeff_of_folded_system

theorem RegularSingular.exists_expansion_coeff_of_folded_system
    {n J R d₂ d : ℕ} (e : Fin n → ℂ) (he : Function.Injective e)
    (P : Type*) [TopologicalSpace P]
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (L : ℝ) (hMc : ∀ a, Continuous fun p => Mc p a) (hMcL : ∀ p a i j, ‖Mc p a i j‖ ≤ L)
    (hA : ∀ k a, Continuous fun p => A p k a) (hAL : ∀ p k a, ‖A p k a‖ ≤ L)
    (q : Polynomial ℂ) (hq : q ≠ 0) (hann : ∀ p, Polynomial.aeval (Mc p 0) q = 0)
    (c c' : P → Fin n → Fin J → ℝ → (Fin R → ℂ))
    (hcont : ∀ i j, ContinuousOn (fun w : P × ℝ => c w.1 i j w.2) (Set.univ ×ˢ Set.Ioc 0 1))
    (hsys : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (c p i j) (c' p i j z) z ∧
      (z : ℂ) • c' p i j z = ∑ a : Fin (d₂ + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
        Matrix.mulVec (Mc p a) (c p i' j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A p k a (c p i' j z)
      else 0)
    (m : ℝ) (B : P → ℝ) (hB : ∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀)
    (hbound : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖c p i j z‖ ≤ B p * z ^ (-m))
    (ρ₂ θ : ℝ) (hθ : ∀ e' : ℂ, q.IsRoot e' → ∀ N : ℕ, ρ₂ < (e' + N).re → θ < (e' + N).re) :
    ∃ (D : ℕ) (S : Finset ℂ) (κ : ℝ), D ≤ n * q.natDegree ∧
      (∀ μ ∈ S, μ.re ≤ ρ₂ ∧ ∃ (e' : ℂ) (N : ℕ), q.IsRoot e' ∧ μ = e' + N) ∧
      ∃ c₂ : ℂ → ℕ → P → Fin n → Fin J → (Fin R → ℂ),
        (∀ μ j₂ i j, Continuous fun p => c₂ μ j₂ p i j) ∧
        ∀ p i j, (∀ μ j₂, ‖c₂ μ j₂ p i j‖ ≤ κ * B p) ∧
          ∀ z ∈ Set.Ioc (0 : ℝ) 1,
            ‖c p i j z - ∑ μ ∈ S, ∑ j₂ ∈ Finset.range D,
                ((z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂) • c₂ μ j₂ p i j‖ ≤ κ * B p * z ^ θ := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_exists_expansion_coeff_of_folded_system.solution

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Instances.Matrix
import P2M.Util
import P2M.Sol.S_RegularSingular_exists_twoLevel_expansion_of_commuting_systems

set_option autoImplicit false

theorem RegularSingular.exists_twoLevel_expansion_of_commuting_systems
    {n J R d d₂ d' d₂' : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (q q' : Polynomial ℂ) (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hcov : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hcov' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, (e₀ + k).re ≤ ρ → ∃ i, e i = e₀ + k)
    (hgq : ∀ e₀ : ℂ, q.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hgq' : ∀ e₀ : ℂ, q'.IsRoot e₀ → ∀ k : ℕ, ρ < (e₀ + k).re → ρ + 2 * δ ≤ (e₀ + k).re)
    (hJ : q.natDegree ≤ J) (hJ' : n * q'.natDegree ≤ J)
    (P : Type*) [TopologicalSpace P]
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (Mc' : P → Fin (d₂' + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A' : P → Fin d' → Fin (d₂' + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (hMc : ∀ b, Continuous fun p => Mc p b) (hA : ∀ k b, Continuous fun p => A p k b)
    (hMc' : ∀ a, Continuous fun p => Mc' p a) (hA' : ∀ k a, Continuous fun p => A' p k a)
    (L : ℝ) (hMcL : ∀ p b i j, ‖Mc p b i j‖ ≤ L) (hAL : ∀ p k b, ‖A p k b‖ ≤ L)
    (hMcL' : ∀ p a i j, ‖Mc' p a i j‖ ≤ L) (hAL' : ∀ p k a, ‖A' p k a‖ ≤ L)
    (hq0 : ∀ p, ∀ z : ℝ, 0 < z → Polynomial.aeval (∑ b : Fin (d₂ + 1), ((z : ℂ) ^ (b : ℕ)) • Mc p b) q = 0)
    (hq0' : ∀ p, ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d₂' + 1), ((y : ℂ) ^ (a : ℕ)) • Mc' p a) q' = 0)
    (Z : ℝ) (hZ : 2 ≤ Z)
    (F Fy Fz : P → ℝ → ℝ → (Fin R → ℂ))
    (hF : ContinuousOn (fun w : P × ℝ × ℝ => F w.1 w.2.1 w.2.2) (Set.univ ×ˢ Set.Ioc 0 1 ×ˢ Set.Ioc 0 Z))
    (hsysY : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      HasDerivAt (fun y => F p y z) (Fy p y z) y ∧
      (y : ℂ) • Fy p y z =
        (fun i => ∑ j, (∑ b : Fin (d₂ + 1), (z : ℂ) ^ (b : ℕ) * Mc p b i j) • F p y z j) +
          ∑ k : Fin d, ∑ b : Fin (d₂ + 1), ((y : ℂ) ^ ((k : ℕ) + 1) * (z : ℂ) ^ (b : ℕ)) • A p k b (F p y z))
    (hsysZ : ∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) Z,
      HasDerivAt (fun z => F p y z) (Fz p y z) z ∧
      (z : ℂ) • Fz p y z =
        (fun i => ∑ j, (∑ a : Fin (d₂' + 1), (y : ℂ) ^ (a : ℕ) * Mc' p a i j) • F p y z j) +
          ∑ k : Fin d', ∑ a : Fin (d₂' + 1), ((z : ℂ) ^ ((k : ℕ) + 1) * (y : ℂ) ^ (a : ℕ)) • A' p k a (F p y z))
    (m B : ℝ)
    (hbound : ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y z‖ ≤ B * y ^ (-m) * z ^ (-m)) :
    ∃ (c : Fin n → Fin J → P → ℝ → (Fin R → ℂ)) (c₂ : Fin n → Fin J → Fin n → Fin J → P → (Fin R → ℂ))
      (C : ℝ),
      (∀ i j, ContinuousOn (fun w : P × ℝ => c i j w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 Z)) ∧
      (∀ i j i' j', Continuous (c₂ i j i' j')) ∧
      (∀ p i j i' j', ‖c₂ i j i' j' p‖ ≤ C) ∧
      (∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ‖c i j p z‖ ≤ C * z ^ (-m)) ∧
      (∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) Z, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F p y z - ∑ i : Fin n, ∑ j : Fin J,
            ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) • c i j p z‖ ≤ C * z ^ (-m) * y ^ (ρ + δ)) ∧
      (∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1,
        ‖c i j p z - ∑ i' : Fin n, ∑ j' : Fin J,
            ((z : ℂ) ^ e i' * ((Real.log z : ℝ) : ℂ) ^ (j' : ℕ)) • c₂ i j i' j' p‖ ≤ C * z ^ (ρ + δ)) := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_exists_twoLevel_expansion_of_commuting_systems.solution

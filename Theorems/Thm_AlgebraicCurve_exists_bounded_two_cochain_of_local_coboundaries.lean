import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries

set_option autoImplicit false

open Polynomial

universe u

theorem AlgebraicCurve.exists_bounded_two_cochain_of_local_coboundaries
    (K : Type u) [Field K] (n : ℕ) (d : Fin (n + 1) → ℕ)
    (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (a : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X])
    (hloc : ∀ P : Ideal K[X], P.IsMaximal → ∃ s : K[X], s ∉ P ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
          (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = s * a i j l m)
    (hinfty : ∃ t : K[X], t ≠ 0 ∧
      ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
        (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
        (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ t.natDegree + d i + d j - d k) ∧
        ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
          (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = t * a i j l m)
    (hgen : ∀ ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, ψ 0 j k = 0) → (∀ i j k, ψ i j k = ψ j i k) →
      (∀ i j l m, (∑ k, ψ j l k * γ i k m) - (∑ k, γ i j k * ψ k l m) +
          (∑ k, γ j l k * ψ i k m) - (∑ k, ψ i j k * γ k l m) = 0) →
      ∃ u : K[X], u ≠ 0 ∧ ∃ lam : Fin (n + 1) → Fin (n + 1) → K[X], (∀ m, lam 0 m = 0) ∧
        ∀ i j m, u * ψ i j m =
          (∑ k, lam j k * γ i k m) - (∑ k, γ i j k * lam k m) + (∑ k, lam i k * γ k j m)) :
    ∃ φ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X],
      (∀ j k, φ 0 j k = 0) ∧ (∀ i j k, φ i j k = φ j i k) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (φ i j k).natDegree ≤ d i + d j - d k) ∧
      ∀ i j l m, (∑ k, φ j l k * γ i k m) - (∑ k, γ i j k * φ k l m) +
        (∑ k, γ j l k * φ i k m) - (∑ k, φ i j k * γ k l m) = a i j l m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_bounded_two_cochain_of_local_coboundaries.solution

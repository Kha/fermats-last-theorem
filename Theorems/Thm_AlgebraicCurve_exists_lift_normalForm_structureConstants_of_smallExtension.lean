import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension

set_option autoImplicit false

open Polynomial

universe u v w w'

theorem AlgebraicCurve.exists_lift_normalForm_structureConstants_of_smallExtension
    (K : Type u) [Field K] [IsAlgClosed K]
    (n : ℕ) (B : Type v) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra K[X] B] (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k)
    (A' : Type w) [CommRing A'] (A : Type w') [CommRing A]
    (π : A' →+* A) (hπ : Function.Surjective π) (ε : A') (hker : ∀ a : A', π a = 0 ↔ ε ∣ a)
    (ρ : A →+* K) (hρ : Function.Surjective ρ)
    (hsmall : ∀ a : A', ρ (π a) = 0 → ε * a = 0)
    (hnil : ∀ a : A', ρ (π a) = 0 → IsNilpotent a)
    (γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A[X])
    (hγ1 : ∀ j k, γ 0 j k = if j = k then 1 else 0)
    (hγc : ∀ i j k, γ i j k = γ j i k)
    (hγa : ∀ i j l m, ∑ k, γ i j k * γ k l m = ∑ k, γ j l k * γ i k m)
    (hγd : ∀ i j k, i ≠ 0 → j ≠ 0 → (γ i j k).natDegree ≤ d i + d j - d k)
    (hγB : ∀ i j k, (γ i j k).map ρ = b.repr (b i * b j) k) :
    ∃ γ' : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → A'[X],
      (∀ j k, γ' 0 j k = if j = k then 1 else 0) ∧
      (∀ i j k, γ' i j k = γ' j i k) ∧
      (∀ i j l m, ∑ k, γ' i j k * γ' k l m = ∑ k, γ' j l k * γ' i k m) ∧
      (∀ i j k, i ≠ 0 → j ≠ 0 → (γ' i j k).natDegree ≤ d i + d j - d k) ∧
      (∀ i j k, (γ' i j k).map π = γ i j k) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_lift_normalForm_structureConstants_of_smallExtension.solution

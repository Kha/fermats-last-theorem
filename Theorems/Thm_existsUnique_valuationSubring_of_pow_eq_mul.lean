import Mathlib
import P2M.Util
import P2M.Sol.S_existsUnique_valuationSubring_of_pow_eq_mul

set_option autoImplicit false

open IsLocalRing Module

theorem existsUnique_valuationSubring_of_pow_eq_mul
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    (n : ℕ) (hn0 : 0 < n) (hn : finrank K L ≤ n)
    (π : R) (hπ : Irreducible π) (u v : L) (huv : u * v = 1) (hu : IsIntegral R u) (hv : IsIntegral R v)
    (ϖ : L) (hϖ : ϖ ^ n = algebraMap R L π * u) :
    finrank K L = n ∧
    ∃ (W : ValuationSubring L) (hRW : ∀ r : R, algebraMap R L r ∈ W),
      (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW r⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      IsDiscreteValuationRing ↥W ∧
      (∃ hϖW : ϖ ∈ W, maximalIdeal ↥W = Ideal.span {(⟨ϖ, hϖW⟩ : ↥W)}) ∧
      (∀ w : ↥W, ∃ r : R, w - ⟨algebraMap R L r, hRW r⟩ ∈ maximalIdeal ↥W) ∧
      (∀ k : K, algebraMap K L k ∈ W ↔ ∃ r : R, algebraMap R K r = k) ∧
      (∀ (W' : ValuationSubring L) (hRW' : ∀ r : R, algebraMap R L r ∈ W'),
        (∀ r ∈ maximalIdeal R, (⟨algebraMap R L r, hRW' r⟩ : ↥W') ∈ maximalIdeal ↥W') → W' = W) := by p2m_exact_reverting @_root_.P2MW.S_existsUnique_valuationSubring_of_pow_eq_mul.solution

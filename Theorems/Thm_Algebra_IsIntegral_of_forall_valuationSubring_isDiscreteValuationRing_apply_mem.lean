import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import P2M.Util
import P2M.Sol.S_Algebra_IsIntegral_of_forall_valuationSubring_isDiscreteValuationRing_apply_mem

set_option autoImplicit false

universe u

theorem Algebra.IsIntegral.of_forall_valuationSubring_isDiscreteValuationRing_apply_mem
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    (h : ∀ (K : Type u) [Field K] (V : ValuationSubring K), IsDiscreteValuationRing V →
      ∀ (φ : B →+* K), (∀ r : R, φ (algebraMap R B r) ∈ V) → ∀ b : B, φ b ∈ V) :
    Algebra.IsIntegral R B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsIntegral_of_forall_valuationSubring_isDiscreteValuationRing_apply_mem.solution

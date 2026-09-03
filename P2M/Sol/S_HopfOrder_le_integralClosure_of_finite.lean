import Mathlib
import P2M.Util
namespace P2MW.S_HopfOrder_le_integralClosure_of_finite

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (S : Subalgebra R A) [Module.Finite R S] : S ≤ integralClosure R A := by
  intro x hx
  rw [mem_integralClosure_iff]
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have h : IsIntegral R (⟨x, hx⟩ : S) := Algebra.IsIntegral.isIntegral _
  exact h.map S.val

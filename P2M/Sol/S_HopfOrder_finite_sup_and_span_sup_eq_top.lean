import Mathlib
import P2M.Util
namespace P2MW.S_HopfOrder_finite_sup_and_span_sup_eq_top

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    [Module.Finite R S] [Module.Finite R S'] (hspan : Submodule.span K (S : Set A) = ⊤) :
    Module.Finite R ↥(S ⊔ S') ∧ Submodule.span K ((S ⊔ S' : Subalgebra R A) : Set A) = ⊤ := by
  refine ⟨Subalgebra.finite_sup S S', ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← hspan]
  exact Submodule.span_mono (fun x hx => (le_sup_left : S ≤ S ⊔ S') hx)

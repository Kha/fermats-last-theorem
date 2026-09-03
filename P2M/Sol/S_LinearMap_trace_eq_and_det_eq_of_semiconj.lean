import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import P2M.Util
namespace P2MW.S_LinearMap_trace_eq_and_det_eq_of_semiconj

theorem solution {R : Type*} {M : Type*} {N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N) (h : ∀ x : M, e (f x) = g (e x)) : LinearMap.trace R M f = LinearMap.trace R N g ∧ LinearMap.det f = LinearMap.det g := by
  have hg : g = e.conj f := by
    ext y
    rw [LinearEquiv.conj_apply]
    simp [h]
  subst hg
  exact ⟨(LinearMap.trace_conj' f e).symm, (LinearMap.det_conj f e).symm⟩

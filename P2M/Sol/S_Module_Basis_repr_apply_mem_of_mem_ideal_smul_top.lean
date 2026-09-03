import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Ideal.Operations
import P2M.Util
namespace P2MW.S_Module_Basis_repr_apply_mem_of_mem_ideal_smul_top

theorem solution {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] {κ : Type*} (b : Module.Basis κ R N) (I : Ideal R) {x : N} (hx : x ∈ (I • ⊤ : Submodule R N)) (k : κ) :
    b.repr x k ∈ I := by
  refine Submodule.smul_induction_on hx (fun a ha n _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy

import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import P2M.Util
namespace P2MW.S_Matrix_exists_generalLinearGroup_forall_algHom_apply_eq_conj

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n K →ₐ[K] Matrix n n K) :
    ∃ u : GL n K, ∀ x : Matrix n n K,
      f x = (u : Matrix n n K) * x * ((u⁻¹ : GL n K) : Matrix n n K) := by
  have hinj : Function.Injective f := RingHom.injective f.toRingHom
  have hsurj : Function.Surjective f := LinearMap.surjective_of_injective (f := f.toLinearMap) hinj
  let F : Matrix n n K ≃ₐ[K] Matrix n n K := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hF : ∀ x, F x = f x := fun _ => rfl
  let G : Module.End K (n → K) ≃ₐ[K] Module.End K (n → K) :=
    (Matrix.toLinAlgEquiv'.symm.trans F).trans Matrix.toLinAlgEquiv'
  obtain ⟨T, hT⟩ := G.eq_linearEquivConjAlgEquiv
  have hG : ∀ x : Matrix n n K, Matrix.toLin' (f x) = T.toLinearMap ∘ₗ Matrix.toLin' x ∘ₗ T.symm.toLinearMap := by
    intro x
    have e0 : ∀ y : Matrix n n K, Matrix.toLin' y = Matrix.toLinAlgEquiv' y := fun _ => rfl
    have h1 : G (Matrix.toLin' x) = Matrix.toLin' (f x) := by
      show Matrix.toLinAlgEquiv' (F (Matrix.toLinAlgEquiv'.symm (Matrix.toLin' x))) = Matrix.toLin' (f x)
      rw [e0, e0, AlgEquiv.symm_apply_apply, hF]
    rw [← h1, hT, LinearEquiv.conjAlgEquiv_apply]
  refine ⟨⟨LinearMap.toMatrix' T.toLinearMap, LinearMap.toMatrix' T.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · intro x
    have h := congrArg LinearMap.toMatrix' (hG x)
    rw [LinearMap.toMatrix'_toLin'] at h
    rw [h, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
    rfl

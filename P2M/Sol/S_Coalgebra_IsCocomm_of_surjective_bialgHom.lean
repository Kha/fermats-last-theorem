import Mathlib
import P2M.Util
namespace P2MW.S_Coalgebra_IsCocomm_of_surjective_bialgHom
set_option autoImplicit false
open scoped TensorProduct

theorem solution
    {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
    {B : Type*} [Semiring B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Coalgebra.IsCocomm R B := by
  refine ⟨LinearMap.ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hπ b
  have h0 := LinearMap.congr_fun (CoalgHomClass.map_comp_comul (π : A →ₐc[R] B)) a
  simp only [LinearMap.comp_apply] at h0
  have hc : Coalgebra.comul (R := R) (π a) =
      TensorProduct.map (π : A →ₐc[R] B).toLinearMap (π : A →ₐc[R] B).toLinearMap
        (Coalgebra.comul (R := R) a) := h0.symm
  show TensorProduct.comm R B B (Coalgebra.comul (R := R) (π a)) = Coalgebra.comul (R := R) (π a)
  rw [hc]
  have hnat : ∀ w : A ⊗[R] A, TensorProduct.comm R B B
      (TensorProduct.map (π : A →ₐc[R] B).toLinearMap (π : A →ₐc[R] B).toLinearMap w) =
      TensorProduct.map (π : A →ₐc[R] B).toLinearMap (π : A →ₐc[R] B).toLinearMap (TensorProduct.comm R A A w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [hnat, Coalgebra.comm_comul]

import Mathlib
import P2M.Util
import P2M.Sol.S_BialgHom_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq

set_option autoImplicit false
universe u

open scoped TensorProduct

theorem BialgHom.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
    (O : Type u) [CommRing O] [IsDomain O] (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (Oh : Type u) [CommRing Oh] [Algebra O Oh]
    (Kh : Type u) [CommRing Kh] [Algebra O Kh] [Algebra K Kh] [Algebra Oh Kh] [IsScalarTower O K Kh] [IsScalarTower O Oh Kh]
    (hinj : Function.Injective (algebraMap Oh Kh))
    (hcap : ∀ (x : K) (y : Oh), algebraMap K Kh x = algebraMap Oh Kh y → ∃ z : O, algebraMap O K z = x)
    (A : Type u) [CommRing A] [Bialgebra O A] [Module.Free O A] [Module.Finite O A]
    (B : Type u) [CommRing B] [Bialgebra O B] [Module.Free O B] [Module.Finite O B]
    (gK : K ⊗[O] B →ₐc[K] K ⊗[O] A) (gOh : Oh ⊗[O] B →ₐc[Oh] Oh ⊗[O] A)
    (hagree : ∀ b : B,
      ((IsScalarTower.toAlgHom O K Kh).toLinearMap.rTensor A) (gK ((1 : K) ⊗ₜ b)) =
        ((IsScalarTower.toAlgHom O Oh Kh).toLinearMap.rTensor A) (gOh ((1 : Oh) ⊗ₜ b))) :
    ∃! g : B →ₐc[O] A,
      Bialgebra.TensorProduct.map (BialgHom.id K K) g = gK ∧ Bialgebra.TensorProduct.map (BialgHom.id Oh Oh) g = gOh := by p2m_exact_reverting @_root_.P2MW.S_BialgHom_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq.solution

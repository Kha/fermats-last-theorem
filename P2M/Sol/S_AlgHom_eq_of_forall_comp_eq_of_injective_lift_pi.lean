import Mathlib
import P2M.Util
namespace P2MW.S_AlgHom_eq_of_forall_comp_eq_of_injective_lift_pi
set_option autoImplicit false

open scoped TensorProduct

namespace AlgHom
p2m_export "AlgHom" "ext comp"
p2m_open "AlgHom"
namespace PointsSeparate

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {A : Type*} [CommRing A] [Algebra K A]
  {P : Type*} (pt : P → (A →ₐ[K] L))

theorem lift_includeRight (a : A) :
    (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L))
      (Algebra.TensorProduct.includeRight a) = fun p => pt p a := by
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

theorem eq_of_forall_apply_eq
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    {a a' : A} (h : ∀ p : P, pt p a = pt p a') : a = a' := by
  have hinc : Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective
  apply hinc
  apply hinj
  rw [lift_includeRight, lift_includeRight]
  funext p
  exact h p

end PointsSeparate
end AlgHom

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A : Type*} [CommRing A] [Algebra K A]
    {P : Type*} (pt : P → (A →ₐ[K] L))
    (hinj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId L (P → L)) (Pi.algHom K _ fun p : P => pt p)
        (fun _ _ => Commute.all _ _) : L ⊗[K] A →ₐ[L] (P → L)))
    {B : Type*} [Semiring B] [Algebra K B] (u u' : B →ₐ[K] A)
    (h : ∀ p : P, (pt p).comp u = (pt p).comp u') :
    u = u' := by
  apply AlgHom.ext
  intro b
  exact AlgHom.PointsSeparate.eq_of_forall_apply_eq pt hinj fun p => DFunLike.congr_fun (h p) b

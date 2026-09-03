import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_bijective_convMul_comp_includeRight_baseChange

set_option autoImplicit false

open scoped TensorProduct

theorem Bialgebra.bijective_convMul_comp_includeRight_baseChange
    (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    (H : Type*) [Ring H] [Bialgebra A H]
    (T : Type*) [CommRing T] [Algebra A T] [Algebra B T] [IsScalarTower A B T] :
    Function.Bijective (fun f : WithConv (B ⊗[A] H →ₐ[B] T) =>
        WithConv.toConv ((f.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)) ∧
      (∀ f g : WithConv (B ⊗[A] H →ₐ[B] T),
        WithConv.toConv (((f * g).ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)
          = WithConv.toConv ((f.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight) *
            WithConv.toConv ((g.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)) ∧
      WithConv.toConv (((1 : WithConv (B ⊗[A] H →ₐ[B] T)).ofConv.restrictScalars A).comp
          Algebra.TensorProduct.includeRight) = (1 : WithConv (H →ₐ[A] T)) ∧
      ∀ (T' : Type*) [CommRing T'] [Algebra A T'] [Algebra B T'] [IsScalarTower A B T']
        (u : T →ₐ[B] T') (f : WithConv (B ⊗[A] H →ₐ[B] T)),
        WithConv.toConv (((u.comp f.ofConv).restrictScalars A).comp Algebra.TensorProduct.includeRight)
          = WithConv.toConv ((u.restrictScalars A).comp
              ((f.ofConv.restrictScalars A).comp Algebra.TensorProduct.includeRight)) := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_bijective_convMul_comp_includeRight_baseChange.solution

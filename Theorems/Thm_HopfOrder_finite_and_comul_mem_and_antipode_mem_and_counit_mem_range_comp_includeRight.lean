import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight

universe u v w
open scoped TensorProduct in

theorem HopfOrder.finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight
    {R : Type u} [CommRing R] {F : Type v} [Field F] [Algebra R F]
    {H : Type w} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {A : Type*} [CommRing A] [HopfAlgebra F A] [Algebra R A] [IsScalarTower R F A]
    (ψ : (F ⊗[R] H) →ₐc[F] A) :
    let S : Subalgebra R A :=
      (((ψ : (F ⊗[R] H) →ₐ[F] A).restrictScalars R).comp
        (Algebra.TensorProduct.includeRight : H →ₐ[R] F ⊗[R] H)).range
    Module.Finite R ↥S ∧
    (∀ x ∈ S, Coalgebra.comul (R := F) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[F] A ⊗[F] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[F] A ⊗[F] A).restrictScalars R).comp S.val)).range) ∧
    (∀ x ∈ S, HopfAlgebra.antipode F (A := A) x ∈ S) ∧
    (∀ x ∈ S, Coalgebra.counit (R := F) (A := A) x ∈ (algebraMap R F).range) := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_finite_and_comul_mem_and_antipode_mem_and_counit_mem_range_comp_includeRight.solution

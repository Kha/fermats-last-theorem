import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfOrder_exists_dual_hopfOrder
attribute [-simp] HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul

set_option autoImplicit false

open scoped TensorProduct

theorem HopfOrder.exists_dual_hopfOrder
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Algebra R (CartierDual K A)] [IsScalarTower R K (CartierDual K A)]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ S' : Subalgebra R (CartierDual K A),
      (∀ φ : CartierDual K A, φ ∈ S' ↔ ∀ b ∈ S, φ b ∈ (algebraMap R K).range) ∧
      Module.Finite R ↥S' ∧ Submodule.span K (S' : Set (CartierDual K A)) = ⊤ ∧
      (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : CartierDual K A →ₐ[K] CartierDual K A ⊗[K] CartierDual K A).restrictScalars R).comp S'.val)).range) ∧
      (∀ x ∈ S', HopfAlgebra.antipode K (A := CartierDual K A) x ∈ S') ∧
      (∀ x ∈ S', Coalgebra.counit (R := K) (A := CartierDual K A) x ∈ (algebraMap R K).range) := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_exists_dual_hopfOrder.solution

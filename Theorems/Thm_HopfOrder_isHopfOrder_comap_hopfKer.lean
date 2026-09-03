import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import P2M.Util
import P2M.Sol.S_HopfOrder_isHopfOrder_comap_hopfKer

open scoped TensorProduct
theorem HopfOrder.isHopfOrder_comap_hopfKer
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) :
    Module.Finite R ↥((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))) ∧
    Submodule.span K (((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)) : Subalgebra R ↥(HopfAlgebra.hopfKer π)) : Set ↥(HopfAlgebra.hopfKer π)) = ⊤ ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : ↥(HopfAlgebra.hopfKer π) →ₐ[K] ↥(HopfAlgebra.hopfKer π) ⊗[K] ↥(HopfAlgebra.hopfKer π)).restrictScalars R).comp ((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : ↥(HopfAlgebra.hopfKer π) →ₐ[K] ↥(HopfAlgebra.hopfKer π) ⊗[K] ↥(HopfAlgebra.hopfKer π)).restrictScalars R).comp ((S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), HopfAlgebra.antipode K (A := ↥(HopfAlgebra.hopfKer π)) x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R))) ∧
    (∀ x ∈ (S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)), Coalgebra.counit (R := K) (A := ↥(HopfAlgebra.hopfKer π)) x ∈ (algebraMap R K).range) := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_isHopfOrder_comap_hopfKer.solution

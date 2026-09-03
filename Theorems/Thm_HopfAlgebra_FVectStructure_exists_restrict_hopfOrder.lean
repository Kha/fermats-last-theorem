import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_FVectStructure_exists_restrict_hopfOrder

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.FVectStructure.exists_restrict_hopfOrder
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {F : Type*} [Field F] (σ : HopfAlgebra.FVectStructure F K A)
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hstab : ∀ (a : Fˣ), ∀ x ∈ S, σ.act (a : F) x ∈ S) :
    haveI : Module.Finite R ↥S := hfin
    letI : Bialgebra R ↥S := HopfOrder.bialgebraOfFinite (K := K) S hcomul hcounit
    ∃ τ : HopfAlgebra.FVectStructure F R ↥S, ∀ (a : F) (s : ↥S), ((τ.act a s : ↥S) : A) = σ.act a (s : A) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_FVectStructure_exists_restrict_hopfOrder.solution

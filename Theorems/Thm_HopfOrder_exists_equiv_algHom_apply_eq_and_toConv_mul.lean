import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import P2M.Util
import P2M.Sol.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul

open scoped TensorProduct
theorem HopfOrder.exists_equiv_algHom_apply_eq_and_toConv_mul
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    {L : Type*} [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (P : Subalgebra R L) (hP : ∀ x : L, IsIntegral R x → x ∈ P) :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    ∃ e : (A →ₐ[K] L) ≃ (↥S →ₐ[R] ↥P),
      (∀ (f : A →ₐ[K] L) (x : ↥S), ((e f x : ↥P) : L) = f (x : A)) ∧
      (∀ f g : A →ₐ[K] L,
          WithConv.toConv (e (WithConv.ofConv (WithConv.toConv f * WithConv.toConv g)))
            = WithConv.toConv (e f) * WithConv.toConv (e g)) ∧
      WithConv.toConv (e (WithConv.ofConv (1 : WithConv (A →ₐ[K] L)))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.solution

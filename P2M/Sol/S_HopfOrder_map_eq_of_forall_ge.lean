import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_HopfAlgebra_FVectStructure
import Theorems.Thm_HopfOrder_isHopfOrder_map
import P2M.Util
namespace P2MW.S_HopfOrder_map_eq_of_forall_ge

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hmin : ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → S ≤ T)
    (σ : A ≃ₐc[K] A) :
    S.map (((σ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R) = S := by
  have himg : ∀ τ : A ≃ₐc[K] A, (Module.Finite R ↥(S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)) ∧ Submodule.span K ((S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)) : Set A) = ⊤ ∧
        (∀ x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)), Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)).val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)).val)).range) ∧
        (∀ x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)), HopfAlgebra.antipode K (A := A) x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R))) ∧
        (∀ x ∈ (S.map (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)), Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) := by
    intro τ
    have hsurj : Function.Surjective (τ : A →ₐc[K] A) := fun y => ⟨τ.symm y, by simp⟩
    exact HopfOrder.isHopfOrder_map S hfin hspan hcomul hanti hcounit (τ : A →ₐc[K] A) hsurj

  have hmapmap : ∀ (τ τ' : A ≃ₐc[K] A) (x : A), x ∈ S → (∀ y, τ (τ' y) = y) →
      x ∈ (S.map (((τ' : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R)).map
        (((τ : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R) := by
    intro τ τ' x hx hinv
    refine Subalgebra.mem_map.mpr ⟨τ' x, Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    simpa using hinv x
  apply le_antisymm
  ·
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subalgebra.mem_map.mp hy
    have hx' : x ∈ S.map (((σ.symm : A →ₐc[K] A) : A →ₐ[K] A).restrictScalars R) := hmin _ (himg σ.symm) hx
    obtain ⟨z, hz, rfl⟩ := Subalgebra.mem_map.mp hx'
    simpa using hz
  · exact hmin _ (himg σ)

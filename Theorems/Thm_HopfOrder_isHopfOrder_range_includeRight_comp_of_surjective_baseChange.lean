import Mathlib
import P2M.Util
import P2M.Sol.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange

open scoped TensorProduct
theorem HopfOrder.isHopfOrder_range_includeRight_comp_of_surjective_baseChange
    {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type*} [CommRing H'] [HopfAlgebra R H']
    (φ : H →ₐc[R] H')
    (hφ : Function.Surjective ((φ : H →ₐ[R] H').toLinearMap.baseChange F)) :
    let S : Subalgebra R (F ⊗[R] H') :=
      ((Algebra.TensorProduct.includeRight : H' →ₐ[R] F ⊗[R] H').comp (φ : H →ₐ[R] H')).range
    (Module.Finite R ↥S ∧
    Submodule.span F ((S : Subalgebra R (F ⊗[R] H')) : Set (F ⊗[R] H')) = ⊤ ∧
    (∀ x ∈ S, Coalgebra.comul (R := F) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : (F ⊗[R] H') →ₐ[F] (F ⊗[R] H') ⊗[F] (F ⊗[R] H')).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : (F ⊗[R] H') →ₐ[F] (F ⊗[R] H') ⊗[F] (F ⊗[R] H')).restrictScalars R).comp S.val)).range) ∧
    (∀ x ∈ S, HopfAlgebra.antipode F (A := (F ⊗[R] H')) x ∈ S) ∧
    (∀ x ∈ S, Coalgebra.counit (R := F) (A := (F ⊗[R] H')) x ∈ (algebraMap R F).range)) ∧
    S ≤ (Algebra.TensorProduct.includeRight : H' →ₐ[R] F ⊗[R] H').range := by p2m_exact_reverting @_root_.P2MW.S_HopfOrder_isHopfOrder_range_includeRight_comp_of_surjective_baseChange.solution

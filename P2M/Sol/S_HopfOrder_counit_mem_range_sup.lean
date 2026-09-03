import Mathlib
import P2M.Util
namespace P2MW.S_HopfOrder_counit_mem_range_sup

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    (hS : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hS' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    ∀ x ∈ S ⊔ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range := by
  have key : S ⊔ S' ≤
      Subalgebra.comap ((Bialgebra.counitAlgHom K A).restrictScalars R) (⊥ : Subalgebra R K) := by
    rw [sup_le_iff]
    constructor
    · intro y hy
      rw [Subalgebra.mem_comap, Algebra.mem_bot]
      simpa using hS y hy
    · intro y hy
      rw [Subalgebra.mem_comap, Algebra.mem_bot]
      simpa using hS' y hy
  intro x hx
  have hmem := key hx
  rw [Subalgebra.mem_comap, Algebra.mem_bot] at hmem
  simpa using hmem

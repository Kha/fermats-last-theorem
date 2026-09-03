import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range

open scoped TensorProduct in
theorem HopfAlgebra.exists_hopfOrder_of_basis_structureConstants_mem_range
    (R : Type) [CommRing R] (K : Type) [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (A : Type) [CommRing A] [HopfAlgebra K A] (hAcocomm : Coalgebra.IsCocomm K A)
    (n : ℕ) (b : Module.Basis (Fin n) K A)
    (hmul : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap R K).range)
    (hone : ∀ k, b.repr 1 k ∈ (algebraMap R K).range)
    (hcomul : ∀ i jk, (b.tensorProduct b).repr (Coalgebra.comul (R := K) (b i)) jk
        ∈ (algebraMap R K).range)
    (hcounit : ∀ i, Coalgebra.counit (R := K) (b i) ∈ (algebraMap R K).range)
    (hanti : ∀ i k, b.repr (HopfAlgebra.antipode K (b i)) k ∈ (algebraMap R K).range) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ ψ : (K ⊗[R] H) ≃ₐ[K] A,
        ∀ x, Coalgebra.comul (R := K) (ψ x)
          = (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := K) x) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_hopfOrder_of_basis_structureConstants_mem_range.solution

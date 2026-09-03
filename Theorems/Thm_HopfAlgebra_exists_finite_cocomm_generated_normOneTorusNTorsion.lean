import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_finite_cocomm_generated_normOneTorusNTorsion

open scoped TensorProduct in
theorem HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ (u v : A),
        (u ^ 2 - algebraMap K A c * v ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v)) ∧
        (Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u) ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u + f v * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_finite_cocomm_generated_normOneTorusNTorsion.solution

import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_cocomm_normOneTorus_generators_and_points

open scoped TensorProduct in
theorem HopfAlgebra.exists_cocomm_normOneTorus_generators_and_points
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c) :
    ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra K B),
      Coalgebra.IsCocomm K B ∧
      ∃ (u v : B),
        (u ^ 2 - algebraMap K B c * v ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v)) ∧
        (Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          ∃! f : B →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_cocomm_normOneTorus_generators_and_points.solution

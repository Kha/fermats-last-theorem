import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_cocomm_adjoin_normOneTorus_of_generators_and_points

open scoped TensorProduct in
theorem HopfAlgebra.exists_cocomm_adjoin_normOneTorus_of_generators_and_points
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (B : Type) [CommRing B] [HopfAlgebra K B] (u v : B)
    (hrel : u ^ 2 - algebraMap K B c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hliftB : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! f : B →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : HopfAlgebra K B₀),
      Coalgebra.IsCocomm K B₀ ∧
      ∃ (u₀ v₀ : B₀),
        (Algebra.adjoin K {u₀, v₀} = ⊤) ∧
        (u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀)) ∧
        (Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_cocomm_adjoin_normOneTorus_of_generators_and_points.solution

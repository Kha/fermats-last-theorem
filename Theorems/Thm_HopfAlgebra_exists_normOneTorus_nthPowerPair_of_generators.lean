import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators

open scoped TensorProduct in
theorem HopfAlgebra.exists_normOneTorus_nthPowerPair_of_generators
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B₀ : Type) [CommRing B₀] [HopfAlgebra K B₀] (hcc₀ : Coalgebra.IsCocomm K B₀)
    (u₀ v₀ : B₀)
    (hgen₀ : Algebra.adjoin K {u₀, v₀} = ⊤)
    (hrel₀ : u₀ ^ 2 - algebraMap K B₀ c * v₀ ^ 2 = 1)
    (hcu₀ : Coalgebra.comul (R := K) u₀ = u₀ ⊗ₜ[K] u₀ + c • (v₀ ⊗ₜ[K] v₀))
    (hcv₀ : Coalgebra.comul (R := K) v₀ = u₀ ⊗ₜ[K] v₀ + v₀ ⊗ₜ[K] u₀)
    (hlift₀ : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z) :
    ∃ (P Q : B₀),
      (P ^ 2 - algebraMap K B₀ c * Q ^ 2 = 1) ∧
      (Coalgebra.comul (R := K) P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q)) ∧
      (Coalgebra.comul (R := K) Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P) ∧
      (Coalgebra.counit (R := K) P = 1) ∧
      (Coalgebra.counit (R := K) Q = 0) ∧
      (∀ f : B₀ →ₐ[K] AlgebraicClosure K,
        f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
        f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_normOneTorus_nthPowerPair_of_generators.solution

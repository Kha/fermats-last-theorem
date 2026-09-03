import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist

open scoped TensorProduct in
theorem HopfAlgebra.exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (A : Type) [CommRing A] [HopfAlgebra K A] (u v : A)
    (hrel : u ^ 2 - algebraMap K A c * v ^ 2 = 1)
    (hcu : Coalgebra.comul (R := K) u = u ⊗ₜ[K] u + c • (v ⊗ₜ[K] v))
    (hcv : Coalgebra.comul (R := K) v = u ⊗ₜ[K] v + v ⊗ₜ[K] u)
    (hn : ∀ f : A →ₐ[K] AlgebraicClosure K, (f u + f v * δ) ^ n = 1)
    (hlift : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u = w ∧ f v = z) :
    ∃ eμ : WithConv (A →ₐ[K] AlgebraicClosure K) ≃ rootsOfUnity n (AlgebraicClosure K),
      (∀ f g, eμ (f * g) = eμ f * eμ g) ∧
      ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
        (∀ a : A, g a = σ (f a)) →
        (σ δ = δ →
          ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          = σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ∧
        (σ δ = -δ →
          ((eμ g : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)
          * σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist.solution

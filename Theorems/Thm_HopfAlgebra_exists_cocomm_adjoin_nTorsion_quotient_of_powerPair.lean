import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_cocomm_adjoin_nTorsion_quotient_of_powerPair

open scoped TensorProduct in
theorem HopfAlgebra.exists_cocomm_adjoin_nTorsion_quotient_of_powerPair
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
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z)
    (P Q : B₀)
    (hrelPQ : P ^ 2 - algebraMap K B₀ c * Q ^ 2 = 1)
    (hcP : Coalgebra.comul (R := K) P = P ⊗ₜ[K] P + c • (Q ⊗ₜ[K] Q))
    (hcQ : Coalgebra.comul (R := K) Q = P ⊗ₜ[K] Q + Q ⊗ₜ[K] P)
    (hεP : Coalgebra.counit (R := K) P = 1)
    (hεQ : Coalgebra.counit (R := K) Q = 0)
    (hpow : ∀ f : B₀ →ₐ[K] AlgebraicClosure K,
      f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
      f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Coalgebra.IsCocomm K A ∧
      ∃ (u' v' : A),
        (Algebra.adjoin K {u', v'} = ⊤) ∧
        (u' ^ 2 - algebraMap K A c * v' ^ 2 = 1) ∧
        (Coalgebra.comul (R := K) u' = u' ⊗ₜ[K] u' + c • (v' ⊗ₜ[K] v')) ∧
        (Coalgebra.comul (R := K) v' = u' ⊗ₜ[K] v' + v' ⊗ₜ[K] u') ∧
        (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
        (∀ (w z : AlgebraicClosure K),
          w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
          (w + z * δ) ^ n = 1 →
          ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_cocomm_adjoin_nTorsion_quotient_of_powerPair.solution

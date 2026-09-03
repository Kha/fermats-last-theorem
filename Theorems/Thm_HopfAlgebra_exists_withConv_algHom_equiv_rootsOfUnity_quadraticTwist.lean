import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist

theorem HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
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
            * σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist.solution

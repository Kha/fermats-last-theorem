import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_finite_cocomm_generated_normOneTorusNTorsion
import Theorems.Thm_HopfAlgebra_exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
import P2M.Util
namespace P2MW.S_HopfAlgebra_exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist

open scoped TensorProduct

theorem solution
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
            * σ ((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) = 1) := by
  obtain ⟨A, iCR, iHA, hFin, hCC, u, v, hrel, hcu, hcv, hn, hlift⟩ :=
    HopfAlgebra.exists_finite_cocomm_generated_normOneTorusNTorsion K c hc hnsq n δ hδ
  letI := iCR; letI := iHA
  exact ⟨A, iCR, iHA, hFin, hCC,
    HopfAlgebra.exists_withConv_equiv_rootsOfUnity_of_comul_gens_quadraticTwist
      K c hc hnsq n δ hδ A u v hrel hcu hcv hn hlift⟩

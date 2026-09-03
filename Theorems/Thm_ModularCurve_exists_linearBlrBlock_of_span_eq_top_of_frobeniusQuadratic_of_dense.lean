import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense {J : Type} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (h2 : (2 : HeckeAlg ⧸ 𝔪) ≠ 0)
    (hspan : Submodule.span (HeckeAlg ⧸ 𝔪)
      (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)) = ⊤)
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
          Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J)))
    (hfin : Finite (heckeTorsion J 𝔪)) (hne : heckeTorsion J 𝔪 ≠ ⊥) :
    ∃ ι : (Fin 2 → HeckeAlg ⧸ 𝔪) →ₗ[HeckeAlg ⧸ 𝔪] heckeTorsion J 𝔪, Function.Injective ι ∧
      ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (v : Fin 2 → HeckeAlg ⧸ 𝔪),
        ι ((ρ σ).mulVec v) = mTorsionGaloisRep J 𝔪 σ (ι v) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_linearBlrBlock_of_span_eq_top_of_frobeniusQuadratic_of_dense.solution

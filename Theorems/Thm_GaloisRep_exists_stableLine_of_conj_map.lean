import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_stableLine_of_conj_map
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

theorem GaloisRep.exists_stableLine_of_conj_map
    (p : ℕ) [Fact p.Prime] {F F' : Type} [Field F] [Field F'] (e : F →+* F')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F')
    (g : GL (Fin 2) F') (hconj : ∀ σ, (ρ' σ).val = g.val * (ρ σ).val.map e * (g⁻¹).val)
    (kn : ℕ) (ap : F)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (h' : ∃ v' : Fin 2 → F', v' ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, Matrix.mulVec (ρ' σ).val v' ∈ F' ∙ v') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F', Matrix.mulVec (ρ' σ).val w - w ∈ F' ∙ v') ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : Fin 2 → F', Matrix.mulVec (ρ' σ).val w - e ap • w ∈ F' ∙ v') ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          Matrix.mulVec (ρ' σ).val v' = ((a : F') ^ (kn - 1)) • v')) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, Matrix.mulVec (ρ σ).val v ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - w ∈ F ∙ v) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : Fin 2 → F, Matrix.mulVec (ρ σ).val w - ap • w ∈ F ∙ v) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          Matrix.mulVec (ρ σ).val v = ((a : F) ^ (kn - 1)) • v) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_stableLine_of_conj_map.solution

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRep_forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd

set_option autoImplicit false

theorem GaloisRep.forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [CharP F p]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hirr : ∀ u : Fin 2 → F, u ≠ 0 →
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Matrix.mulVec (ρ σ).val u ∉ F ∙ u)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) (m : ℕ) (hm : Odd m)
    (hdet : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → (ρ σ).val.det = (a : F) ^ m)
    {F' : Type} [Field F'] (e : F →+* F') (u : Fin 2 → F') (hu : u ≠ 0) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, Matrix.mulVec ((ρ σ).val.map e) u ∉ F' ∙ u := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd.solution

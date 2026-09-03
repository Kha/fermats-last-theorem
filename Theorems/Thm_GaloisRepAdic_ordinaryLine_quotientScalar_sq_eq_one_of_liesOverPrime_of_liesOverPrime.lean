import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime

set_option autoImplicit false
theorem GaloisRepAdic.ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime)
    (P P' : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hP' : P'.LiesOverPrime p)
    (h' : ∀ L' : Submodule A ρ.V, (∃ b : Module.Basis (Fin 2) A ρ.V, L' = A ∙ b 0) →
      (∀ σ ∈ P'.decompositionSubgroup ℚ, ∀ v ∈ L', ρ.ρ σ v ∈ L') →
      (∀ σ ∈ P'.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L') →
      ∀ σ ∈ P'.decompositionSubgroup ℚ, ∀ z : A,
        (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L') → z * z = 1)
    (L : Submodule A ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (z : A) (hz : ∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) :
    z * z = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime.solution

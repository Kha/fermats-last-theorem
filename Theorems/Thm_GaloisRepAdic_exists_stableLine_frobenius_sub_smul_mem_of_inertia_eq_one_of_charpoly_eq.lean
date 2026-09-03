import Mathlib
import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_inertia_eq_one_of_charpoly_eq
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

open Polynomial

theorem GaloisRepAdic.exists_stableLine_frobenius_sub_smul_mem_of_inertia_eq_one_of_charpoly_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsPrincipalIdealRing A]
    (ρ : GaloisRepAdic A) {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (hI : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ τ = 1)
    (a d α : A) (hα : α * α - a * α + d = 0)
    (hchar : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
      LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C a * X + C d) :
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v : ρ.V, ρ.ρ σ v - α • v ∈ L) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
        ∀ v ∈ L, ρ.ρ σ v = (a - α) • v) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_exists_stableLine_frobenius_sub_smul_mem_of_inertia_eq_one_of_charpoly_eq.solution

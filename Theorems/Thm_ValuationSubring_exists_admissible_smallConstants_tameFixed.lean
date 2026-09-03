import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_admissible_smallConstants_tameFixed
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicClosure.Rat.isGalois
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.exists_admissible_smallConstants_tameFixed
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A),
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))} ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      (∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

      (∀ τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), (∀ x : (AlgebraicClosure ℚ), x ∈ A ↔ τ x ∈ A) →
        ∀ x : (AlgebraicClosure ℚ), x ∈ k₀ → τ x ∈ k₀) ∧

      (∀ π : (AlgebraicClosure ℚ), π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) → π ∈ A →
        ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 → ∀ x : ↥k₀, τ (x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) ∧
      ∃ (ℓ : ℕ), ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧
      ∃ (ζ₀ : ↥k₀), IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ) ∧
      ∃ (ϖt : ↥k₀), (ϖt : AlgebraicClosure ℚ) ∈ A ∧
        ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_admissible_smallConstants_tameFixed.solution

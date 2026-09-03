import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

theorem ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq
    {q : ℕ} (hq' : q.Prime) (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q)
    (L : Type) [Field L] [Algebra L (AlgebraicClosure ℚ)] :
    ∃ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, γ ∈ P.inertiaSubgroupIn ℚ ∧
      (∀ l : L, γ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ q → ∀ (m : ℕ),
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ →
          (∀ l : L, τ (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
          ∃ (j : ℕ) (x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
            x ∈ P.inertiaSubgroupIn ℚ ∧ (∀ l : L, x (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
            w ∈ P.inertiaSubgroupIn ℚ ∧ (∀ l : L, w (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) ∧
            τ = γ ^ j * x ^ (ℓ ^ m) * w ^ (ℓ ^ m) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_forall_apply_algebraMap_eq.solution

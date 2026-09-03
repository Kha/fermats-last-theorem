import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

theorem ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois
    {k L : Type} [Field k] [Field L] [Algebra k L] [IsAlgClosed L] [CharZero L] [IsGalois k L]
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    {q : ℕ} (hq' : q.Prime) (P : ValuationSubring L) (hq : P.LiesOverPrime q) :
    ∃ γ : L ≃ₐ[k] L, γ ∈ P.inertiaSubgroupIn k ∧
      ∀ (p : ℕ), p.Prime → p ≠ q → ∀ (m : ℕ),
        ∀ τ ∈ P.inertiaSubgroupIn k, ∃ (j : ℕ) (x w : L ≃ₐ[k] L),
          x ∈ P.inertiaSubgroupIn k ∧ w ∈ P.inertiaSubgroupIn k ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois.solution

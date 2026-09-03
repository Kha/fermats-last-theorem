import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois
attribute [-instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois
    {k L : Type} [Field k] [Field L] [Algebra k L] [IsAlgClosed L] [CharZero L] [IsGalois k L]
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring L) (hq : P.LiesOverPrime q) (n : ℕ)
    (g : L ≃ₐ[k] L) (hg : g ∈ P.inertiaSubgroupIn k)
    (hrad : ∀ (α : L) (j : ℕ), α ^ (p ^ j) = (q : L) → g α = α) :
    ∃ w ∈ P.inertiaSubgroupIn k, w ^ (p ^ n) = g := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois.solution

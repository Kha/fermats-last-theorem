import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
attribute [-instance] MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup
attribute [-simp] MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective
    (q : ℕ) [Fact q.Prime]
    {V : Type*} [CommRing V] [IsDomain V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V]
    (G : FormalGroup V) [G.IsComm]
    (r : Fin (q * q) → V) (hr : ∀ i, r i ∈ maximalIdeal V) (hinj : Function.Injective r)
    (U : PowerSeries V) (hU : IsUnit U)
    (hq : G.nthSeries q = ((∏ i, (Polynomial.X - Polynomial.C (r i)) : Polynomial V) : PowerSeries V) * U) :
    ∃ α β : V, α ∈ maximalIdeal V ∧ β ∈ maximalIdeal V ∧ G.IsDrinfeldBasisAdic (maximalIdeal V) q α β := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_exists_isDrinfeldBasisAdic_of_nthSeries_eq_prod_mul_of_injective.solution

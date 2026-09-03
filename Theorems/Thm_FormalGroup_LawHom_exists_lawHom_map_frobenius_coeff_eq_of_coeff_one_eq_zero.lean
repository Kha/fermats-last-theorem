import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
attribute [-instance] MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing
attribute [-simp] MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
    {S : Type u} [CommRing S] (q : ℕ) [Fact q.Prime] [CharP S q]
    {F G : FormalGroup S} (θ : FormalGroup.LawHom F G) (h1 : PowerSeries.coeff 1 θ.series = 0) :
    ∃ θ₁ : FormalGroup.LawHom (F.map (frobenius S q)) G,
      ∀ n : ℕ, PowerSeries.coeff n θ₁.series = PowerSeries.coeff (q * n) θ.series := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero.solution

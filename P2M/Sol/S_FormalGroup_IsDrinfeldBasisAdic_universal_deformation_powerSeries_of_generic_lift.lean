import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_universal_of_universal_sq_zero
import P2M.Util
namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_universal_deformation_powerSeries_of_generic_lift
attribute [-instance] MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing IsLocalRing.SmallExtension.algebra
attribute [-simp] MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' IsLocalRing.SmallExtension.snd_pair IsLocalRing.SmallExtension.res_mk IsLocalRing.SmallExtension.snd_apply IsLocalRing.SmallExtension.coe_diag
attribute [-simp] IsLocalRing.SmallExtension.fst_pair IsLocalRing.SmallExtension.fst_apply FormalGroup.ofPair_toPowerSeries IsLocalRing.SmallExtension.mk_thetaLiftAlgHom FormalGroup.LawIso.map_series IsLocalRing.SmallExtension.fst_pairRingHom FormalGroup.LawIso.ofPair_series FormalGroup.LawHom.ofPair_series IsLocalRing.SmallExtension.snd_pairRingHom IsLocalRing.SmallExtension.snd_pairAlgHom IsLocalRing.SmallExtension.fst_pairAlgHom FormalGroup.LawHom.map_series IsLocalRing.SmallExtension.fst_thetaLift IsLocalRing.SmallExtension.mk_thetaLift IsLocalRing.SmallExtension.fst_thetaLiftAlgHom

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hγ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀) :
    (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
          ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
            (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
            ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
              ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) :=
  FormalGroup.IsDrinfeldBasisAdic.universal_of_universal_sq_zero q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu
    (FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries
      q k W₀ hW₀ res₀ hres₀ hker₀ F₀ hF₀ Fu hFu hγ)

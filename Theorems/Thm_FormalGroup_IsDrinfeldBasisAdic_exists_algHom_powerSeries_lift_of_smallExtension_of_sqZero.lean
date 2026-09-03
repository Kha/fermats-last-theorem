import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsDrinfeldBasisAdic_exists_algHom_powerSeries_lift_of_smallExtension_of_sqZero
attribute [-instance] IsLocalRing.SmallExtension.algebra
attribute [-simp] IsLocalRing.SmallExtension.snd_pair IsLocalRing.SmallExtension.res_mk IsLocalRing.SmallExtension.snd_apply IsLocalRing.SmallExtension.coe_diag IsLocalRing.SmallExtension.fst_pair IsLocalRing.SmallExtension.fst_apply FormalGroup.ofPair_toPowerSeries IsLocalRing.SmallExtension.mk_thetaLiftAlgHom FormalGroup.LawIso.map_series IsLocalRing.SmallExtension.fst_pairRingHom FormalGroup.LawIso.ofPair_series FormalGroup.LawHom.ofPair_series IsLocalRing.SmallExtension.snd_pairRingHom IsLocalRing.SmallExtension.snd_pairAlgHom IsLocalRing.SmallExtension.fst_pairAlgHom FormalGroup.LawHom.map_series IsLocalRing.SmallExtension.fst_thetaLift IsLocalRing.SmallExtension.mk_thetaLift IsLocalRing.SmallExtension.fst_thetaLiftAlgHom

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_lift_of_smallExtension_of_sqZero
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hFu1 : (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) → (maximalIdeal T) ^ 2 = ⊥ → (q : T) = 0 →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
          ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
            (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
            ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
              ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0))

    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (S : Type) [CommRing S] [IsLocalRing S] [IsArtinianRing S] [Algebra W₀ S]
    (resS : S →+* k) (hresS : Function.Surjective resS) (hkerS : RingHom.ker resS = maximalIdeal S)
    (σ : T →ₐ[W₀] S) (hσ : Function.Surjective σ) (hσres : ∀ t : T, resS (σ t) = resT t)
    (hsmall : RingHom.ker σ.toRingHom * maximalIdeal T = ⊥)

    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (Gσ : FormalGroup S) (hGσ : G.IsBaseChange σ.toRingHom Gσ)
    (φbar : PowerSeries W₀ →ₐ[W₀] S)
    (hφbar : ∀ r : PowerSeries W₀, resS (φbar r) = res₀ (PowerSeries.constantCoeff r))
    (Gbar' : FormalGroup S) (hbcbar : Fu.IsBaseChange φbar.toRingHom Gbar') (ψbar : FormalGroup.LawIso Gbar' Gσ)
    (hψbar : ∀ n : ℕ, resS (PowerSeries.coeff n ψbar.series) = if n = 1 then 1 else 0) :
    ∃ φ : PowerSeries W₀ →ₐ[W₀] T,
      σ.comp φ = φbar ∧
      ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
        ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_algHom_powerSeries_lift_of_smallExtension_of_sqZero.solution

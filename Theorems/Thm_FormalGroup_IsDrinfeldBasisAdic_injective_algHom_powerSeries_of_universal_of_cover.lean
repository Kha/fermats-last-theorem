import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal_of_cover

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem FormalGroup.IsDrinfeldBasisAdic.injective_algHom_powerSeries_of_universal_of_cover
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra W₀ R] [IsAdicComplete (maximalIdeal R) R] [IsNoetherianRing R]
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (F : FormalGroup R) [F.IsComm] (hF : F.IsBaseChange resR F₀)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ maximalIdeal R) (hx₁ : x₁ ∈ maximalIdeal R)
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (huniv : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃! φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ x₀) = y₀ ∧ ψ.toLawHom.appAdic (maximalIdeal T) (φ x₁) = y₁)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hLT : (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
          (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
          (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
          ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
            ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
              (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
              ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
                ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0))
    (φ : PowerSeries W₀ →ₐ[W₀] R)
    (hφres : ∀ r : PowerSeries W₀, resR (φ r) = res₀ (PowerSeries.constantCoeff r))
    (F' : FormalGroup R) (hbc : Fu.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' F)
    (hψ : ∀ n : ℕ, resR (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0)
    (C : Type) [CommRing C] [Algebra (PowerSeries W₀) C] [IsLocalRing C]
    [Module.Finite (PowerSeries W₀) C] [IsAdicComplete (maximalIdeal C) C]
    (resC : C →+* k) (hresC : Function.Surjective resC) (hkerC : RingHom.ker resC = maximalIdeal C)
    (hresC₀ : ∀ f : PowerSeries W₀, resC (algebraMap (PowerSeries W₀) C f) = res₀ (PowerSeries.constantCoeff f))
    (Gc : FormalGroup C) (hGc : Fu.IsBaseChange (algebraMap (PowerSeries W₀) C) Gc)
    (c₀ c₁ : C) (hc₀ : c₀ ∈ maximalIdeal C) (hc₁ : c₁ ∈ maximalIdeal C)
    (hcD : Gc.IsDrinfeldBasisAdic (maximalIdeal C) q c₀ c₁)
    (hinj : Function.Injective (algebraMap (PowerSeries W₀) C)) :
    Function.Injective φ := by p2m_exact_reverting @_root_.P2MW.S_FormalGroup_IsDrinfeldBasisAdic_injective_algHom_powerSeries_of_universal_of_cover.solution

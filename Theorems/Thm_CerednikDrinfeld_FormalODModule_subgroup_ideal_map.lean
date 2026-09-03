import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_subgroup_ideal_map

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.subgroup_ideal_map
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsNoetherianRing B] (hB : IsNilpotent (p : B))
    (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B)) (h : ℕ)

    (hfin : Module.Finite B (MvPowerSeries (Fin 2) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin 2) B ⧸ I))
    (hrank : ∀ (κ : Type) [Field κ] (f : B →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ I.map (MvPowerSeries.map f)) = p ^ h)

    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hunit : ∀ f ∈ I, MvPowerSeries.constantCoeff f = 0)

    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))

    (hact : ∀ (a : Zp2 p), ∀ f ∈ I, MvPowerSeries.subst (X.act a) f ∈ I)
    (hvarpi : ∀ f ∈ I, MvPowerSeries.subst X.varpi f ∈ I)
    {B' : Type} [CommRing B'] (φ : B →+* B') :
    Module.Finite B' (MvPowerSeries (Fin 2) B' ⧸ I.map (MvPowerSeries.map φ)) ∧
    Module.Projective B' (MvPowerSeries (Fin 2) B' ⧸ I.map (MvPowerSeries.map φ)) ∧
    (∀ (κ : Type) [Field κ] (f : B' →+* κ),
      Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ (I.map (MvPowerSeries.map φ)).map (MvPowerSeries.map f)) = p ^ h) ∧
    (∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B') ^ q ∈ I.map (MvPowerSeries.map φ)) ∧
    (∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.constantCoeff f = 0) ∧
    (∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst (X.map φ).F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
            (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B')) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B'))) ''
            (I.map (MvPowerSeries.map φ) : Set (MvPowerSeries (Fin 2) B')))) ∧
    (∀ (a : Zp2 p), ∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst ((X.map φ).act a) f ∈ I.map (MvPowerSeries.map φ)) ∧
    (∀ f ∈ I.map (MvPowerSeries.map φ), MvPowerSeries.subst (X.map φ).varpi f ∈ I.map (MvPowerSeries.map φ)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_subgroup_ideal_map.solution

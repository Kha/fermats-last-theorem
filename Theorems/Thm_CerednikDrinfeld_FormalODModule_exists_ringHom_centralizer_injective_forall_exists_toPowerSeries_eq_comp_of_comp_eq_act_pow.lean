import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
    {r : ℕ} [Fact r.Prime]
    {k₀ k : Type} [CommRing k₀] [CommRing k] (κ : k₀ →+* k) (hκ : Function.Injective κ)
    (X₀ : FormalODModule r k₀) (Φ : FormalODModule r k)
    (β₀ β₀' : SpecialFormal.Series k) (N : ℕ)
    (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
    (h₁ : β₀'.comp β₀ = Φ.act ((r : Zp2 r) ^ N)) (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N))
    (hc₁ : ∀ σ τ : SpecialFormal.Series k, σ.comp β₀ = τ.comp β₀ → σ = τ)
    (hc₂ : ∀ σ τ : SpecialFormal.Series k, σ.comp (Φ.act ((r : Zp2 r) ^ N)) = τ.comp (Φ.act ((r : Zp2 r) ^ N)) → σ = τ)
    {K₀ : Type} [Field K₀] [CharZero K₀]
    (E₀ : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀) :
    ∃ E : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})) →+* Matrix (Fin 2) (Fin 2) K₀,
      Function.Injective E ∧
      ∀ ε : ↥(Subring.centralizer (Set.range X₀.actEnd ∪ {X₀.varpiEnd})),
        ∃ e : ↥(Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})),
          (e : MvFormalGroup.End Φ.F).toPowerSeries =
            β₀'.comp ((SpecialFormal.Series.map κ (ε : MvFormalGroup.End X₀.F).toPowerSeries).comp β₀) ∧
          E₀ e = ((r : K₀) ^ N) • E ε := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow.solution

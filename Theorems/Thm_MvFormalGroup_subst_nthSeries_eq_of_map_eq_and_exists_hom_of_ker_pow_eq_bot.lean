import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot

set_option autoImplicit false

universe u

theorem MvFormalGroup.subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
    {R S : Type u} [CommRing R] [CommRing S] (π : R →+* S) (μ : ℕ)
    (hI : RingHom.ker π ^ (μ + 1) = ⊥) (p n : ℕ) (hp : (p : R) ^ n = 0)
    {h : ℕ} (G : MvFormalGroup h R) [G.IsComm] :
    (∀ (τ : Type) (a b : Fin h → MvPowerSeries τ R),
        (∀ i, (a i).constantCoeff = 0) → (∀ i, (b i).constantCoeff = 0) →
        (∀ i, MvPowerSeries.map π (a i) = MvPowerSeries.map π (b i)) →
        ∀ i, MvPowerSeries.subst a (G.nthSeries (p ^ (n * μ)) i) =
          MvPowerSeries.subst b (G.nthSeries (p ^ (n * μ)) i)) ∧
    (∀ (g : ℕ) (F : MvFormalGroup g R) (φ : Fin h → MvPowerSeries (Fin g) R),
        (∀ i, (φ i).constantCoeff = 0) →
        (∃ f₀ : (F.map π).Hom (G.map π), ∀ i, f₀.toPowerSeries i = MvPowerSeries.map π (φ i)) →
        ∃ f : F.Hom G, ∀ i, f.toPowerSeries i = MvPowerSeries.subst φ (G.nthSeries (p ^ (n * μ)) i)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot.solution

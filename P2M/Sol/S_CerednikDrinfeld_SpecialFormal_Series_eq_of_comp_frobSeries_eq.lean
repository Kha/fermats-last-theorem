import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Series_eq_of_comp_frobSeries_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace WsFortySix
namespace P4

theorem subst_X_pow_injective {σ : Type} {B : Type} [CommRing B] (q : ℕ) (hq : q ≠ 0)
    (f g : MvPowerSeries σ B)
    (h : MvPowerSeries.subst (fun i => (MvPowerSeries.X i : MvPowerSeries σ B) ^ q) f =
      MvPowerSeries.subst (fun i => (MvPowerSeries.X i : MvPowerSeries σ B) ^ q) g) : f = g := by
  have h' : MvPowerSeries.expand q hq f = MvPowerSeries.expand q hq g := by
    rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply, MvPowerSeries.substAlgHom_apply]
    exact h
  ext m
  rw [← MvPowerSeries.coeff_expand_smul q hq f m, ← MvPowerSeries.coeff_expand_smul q hq g m, h']

end WsFortySix.P4

theorem solution
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (j : ℕ) (φ ψ : Series B)
    (h : φ.comp (Rigidified.frobSeries (p := p) B j) = ψ.comp (Rigidified.frobSeries (p := p) B j)) :
    φ = ψ := by
  funext i
  have hi : MvPowerSeries.subst (Rigidified.frobSeries (p := p) B j) (φ i) =
      MvPowerSeries.subst (Rigidified.frobSeries (p := p) B j) (ψ i) := congr_fun h i
  exact WsFortySix.P4.subst_X_pow_injective (p ^ j) (pow_ne_zero j (Fact.out : p.Prime).ne_zero)
    (φ i) (ψ i) hi

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
    {p : ℕ} [Fact p.Prime] {B R₀ S : Type} [CommRing B] [CommRing R₀] [CommRing S]
    (X : FormalODModule p B) (X₀ : FormalODModule p R₀) (f : B →+* S) (g : R₀ →+* S)
    (σ σf ε : Series S)
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσf0 : ∀ i, MvPowerSeries.constantCoeff (σf i) = 0)
    (hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hlin : ∀ m : ℕ, (Series.map f (X.F.nthSeries m)).comp σf = σf.comp (Series.map g (X₀.F.nthSeries m)))
    (u v α β : ℕ) (hu : IsUnit ((u : ℕ) : Zp2 p)) (hv : IsUnit ((v : ℕ) : Zp2 p))
    (h : (Series.map f (X.F.nthSeries (u * p ^ α))).comp (σ.comp ε) =
      (Series.map f (X.F.nthSeries (u * v * p ^ β))).comp σf) :
    (Series.map f (X.F.nthSeries (p ^ α))).comp (σ.comp (ε.comp (Series.map g (X₀.act ((hv.unit⁻¹ : (Zp2 p)ˣ) : Zp2 p))))) =
      (Series.map f (X.F.nthSeries (p ^ β))).comp σf := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq.solution

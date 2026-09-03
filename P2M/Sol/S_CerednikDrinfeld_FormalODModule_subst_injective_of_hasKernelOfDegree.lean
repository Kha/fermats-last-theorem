import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_residueFields
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_hasKernelOfDegree

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d)
    (f g : MvPowerSeries (Fin 2) B) (h : MvPowerSeries.subst φ f = MvPowerSeries.subst φ g) : f = g :=
  CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_residueFields φ hφ0 hφ.1
    (fun κ _ g' _ hfin => CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_field (φ.map g')
      (fun i => by simp [Series.map, hφ0]) hfin) f g h

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map_of_X_pow_mem
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {B B' : Type u} [CommRing B] [IsNoetherianRing B] [CommRing B'] (g : B →+* B') (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) :
    FormalODModule.HasKernelOfDegree (φ.map g) d := by
  obtain ⟨N, hN⟩ := CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree φ hφ0 hφ
  exact CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map_of_X_pow_mem g φ hφ0 hφ N hN

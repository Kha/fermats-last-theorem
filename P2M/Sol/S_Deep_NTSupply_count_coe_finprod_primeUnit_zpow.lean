import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
namespace P2MW.S_Deep_NTSupply_count_coe_finprod_primeUnit_zpow

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K : Type*) [Field K] [NumberField K]
    (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : (Function.support n).Finite) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w
      (((∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ n v : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)) :
        FractionalIdeal ((𝓞 K)⁰) K) = n w := by
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => primeUnit K v ^ n v).Finite := by
    refine hn.subset fun v hv => ?_
    rw [Function.mem_support]
    intro h
    exact hv (by simp [h])
  have hmap := MonoidHom.map_finprod (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)) hsupp
  simp only [Units.coeHom_apply] at hmap
  rw [hmap]
  simp_rw [Units.val_zpow_eq_zpow_val, primeUnit_val]
  apply FractionalIdeal.count_finprod K w n
  rw [Filter.eventually_cofinite]
  exact hn

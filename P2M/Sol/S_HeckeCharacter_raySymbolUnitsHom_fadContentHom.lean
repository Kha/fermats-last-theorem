import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_count_coe_fadContentHom
import P2M.Util
namespace P2MW.S_HeckeCharacter_raySymbolUnitsHom_fadContentHom

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]
    (f : HeightOneSpectrum (𝓞 K) → M) (y : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    raySymbolUnitsHom K f (fadContentHom K y) = ∏ᶠ w : HeightOneSpectrum (𝓞 K), f w ^ placeOrd K y w := by
  show ∏ᶠ w : HeightOneSpectrum (𝓞 K), f w ^ FractionalIdeal.count K w
      ((fadContentHom K y : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = _
  exact finprod_congr fun w => by rw [HeckeCharacter.count_coe_fadContentHom]

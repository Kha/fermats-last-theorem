import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_raySymbolUnitsHom_fadContentHom

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem HeckeCharacter.raySymbolUnitsHom_fadContentHom
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommGroup M]
    (f : HeightOneSpectrum (𝓞 K) → M) (y : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    raySymbolUnitsHom K f (fadContentHom K y) = ∏ᶠ w : HeightOneSpectrum (𝓞 K), f w ^ placeOrd K y w := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_raySymbolUnitsHom_fadContentHom.solution

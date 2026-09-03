import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_raySymbolUnitsHom_fadContentHom
import P2M.Util
namespace P2MW.S_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    [IsMulCommutative (M ≃ₐ[K] M)] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣) :
    artinSymbol K M 𝔣 ⟨fadContentHom K (projFin K u), hu⟩ =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K M v ^ placeOrd K (projFin K u) v := by
  show raySymbolUnitsHom K (artinFrob K M) (fadContentHom K (projFin K u)) = _
  exact HeckeCharacter.raySymbolUnitsHom_fadContentHom K (artinFrob K M) (projFin K u)

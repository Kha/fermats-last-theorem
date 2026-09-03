import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem LanglandsTunnell.P2.Artin.artinSymbol_fadContentHom
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    [IsMulCommutative (M ≃ₐ[K] M)] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣) :
    artinSymbol K M 𝔣 ⟨fadContentHom K (projFin K u), hu⟩ =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinFrob K M v ^ placeOrd K (projFin K u) v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_artinSymbol_fadContentHom.solution

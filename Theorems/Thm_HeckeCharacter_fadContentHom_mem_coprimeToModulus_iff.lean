import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem HeckeCharacter.fadContentHom_mem_coprimeToModulus_iff
    (K : Type*) [Field K] [NumberField K] {𝔣 : Ideal (𝓞 K)} (y : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K y ∈ coprimeToModulus K 𝔣 ↔
      ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 → placeOrd K y w = 0 := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff.solution

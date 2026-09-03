import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_count_coe_fadContentHom
import P2M.Util
namespace P2MW.S_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K : Type*) [Field K] [NumberField K] {𝔣 : Ideal (𝓞 K)} (y : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K y ∈ coprimeToModulus K 𝔣 ↔
      ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 → placeOrd K y w = 0 := by
  simp only [mem_coprimeToModulus_iff, HeckeCharacter.count_coe_fadContentHom]

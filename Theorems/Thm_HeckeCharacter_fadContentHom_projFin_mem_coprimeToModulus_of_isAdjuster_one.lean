import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter

theorem HeckeCharacter.fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : IsAdjuster K 𝔣 u 1) :
    fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣 := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one.solution

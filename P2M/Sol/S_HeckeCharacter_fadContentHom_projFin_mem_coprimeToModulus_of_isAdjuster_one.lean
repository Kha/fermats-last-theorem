import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Theorems.Thm_HeckeCharacter_fadContentHom_mem_coprimeToModulus_iff
import P2M.Util
namespace P2MW.S_HeckeCharacter_fadContentHom_projFin_mem_coprimeToModulus_of_isAdjuster_one

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin Deep.NTSupply

theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : IsAdjuster K 𝔣 u 1) :
    fadContentHom K (projFin K u) ∈ coprimeToModulus K 𝔣 := by
  rw [HeckeCharacter.fadContentHom_mem_coprimeToModulus_iff]
  intro w hw
  rw [placeOrd_eq_zero_iff]
  have h := (hu.cong w hw).1
  rw [map_one, inv_one, mul_one] at h
  exact h

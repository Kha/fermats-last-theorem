import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_exists_isAdjuster_one_and_fadContentHom_projFin_eq

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem HeckeCharacter.exists_isAdjuster_one_and_fadContentHom_projFin_eq
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (J : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)
    (hJ : J ∈ coprimeToModulus K 𝔣) :
    ∃ x : (AdeleRing (𝓞 K) K)ˣ, IsAdjuster K 𝔣 x 1 ∧ (x : AdeleRing (𝓞 K) K).1 = 1 ∧
      fadContentHom K (projFin K x) = J := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_exists_isAdjuster_one_and_fadContentHom_projFin_eq.solution

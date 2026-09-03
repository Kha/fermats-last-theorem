import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_coe_fadContentHom_projFin_unitsMap_algebraMap

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem HeckeCharacter.coe_fadContentHom_projFin_unitsMap_algebraMap
    (K : Type*) [Field K] [NumberField K] (α : Kˣ) :
    ((fadContentHom K (projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α)) :
        (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (α : K) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_coe_fadContentHom_projFin_unitsMap_algebraMap.solution

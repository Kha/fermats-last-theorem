import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (β : Lˣ) :
    fracRelNormUnit K L
        (fadContentHom L (projFin L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) β))) =
      fadContentHom K (projFin K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.map (Algebra.norm K : L →* K) β))) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_fracRelNormUnit_fadContentHom_projFin_unitsMap_algebraMap.solution

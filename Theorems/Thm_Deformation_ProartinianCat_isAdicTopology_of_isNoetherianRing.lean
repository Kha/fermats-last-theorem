import Mathlib
import Definitions.Def_Deformations_ProartinianCat
import P2M.Util
import P2M.Sol.S_Deformation_ProartinianCat_isAdicTopology_of_isNoetherianRing
attribute [-instance] Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace

set_option autoImplicit false
open IsLocalRing

universe u
theorem Deformation.ProartinianCat.isAdicTopology_of_isNoetherianRing
    {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [Finite (ResidueField 𝓞)]
    (R : Deformation.ProartinianCat 𝓞) [IsNoetherianRing R] :
    IsLocalRing.IsAdicTopology R := by p2m_exact_reverting @_root_.P2MW.S_Deformation_ProartinianCat_isAdicTopology_of_isNoetherianRing.solution

import Definitions.Def_Deformations_ProartinianCat
import P2M.Util
import P2M.Sol.S_IsLocalRing_isLocalProartinianAlgebra_adicTopology

universe u
open IsLocalRing Deformation
theorem IsLocalRing.isLocalProartinianAlgebra_adicTopology
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
    (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap 𝒪 R))) :
    letI : TopologicalSpace R := (maximalIdeal R).adicTopology
    IsLocalProartinianAlgebra 𝒪 R := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isLocalProartinianAlgebra_adicTopology.solution

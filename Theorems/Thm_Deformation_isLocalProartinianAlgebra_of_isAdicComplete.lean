import Mathlib
import Definitions.Def_Deformations_ProartinianCat
import P2M.Util
import P2M.Sol.S_Deformation_isLocalProartinianAlgebra_of_isAdicComplete

set_option autoImplicit false

open IsLocalRing
theorem Deformation.isLocalProartinianAlgebra_of_isAdicComplete
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A)) :
    @Deformation.IsLocalProartinianAlgebra 𝒪 _ A _ (maximalIdeal A).adicTopology _ := by p2m_exact_reverting @_root_.P2MW.S_Deformation_isLocalProartinianAlgebra_of_isAdicComplete.solution

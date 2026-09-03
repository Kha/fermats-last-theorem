import Mathlib
import Definitions.Def_Deformations_ProartinianCat
import P2M.Util
namespace P2MW.S_Deformation_isLocalProartinianAlgebra_of_isAdicComplete

set_option autoImplicit false

open IsLocalRing

theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A)) :
    @Deformation.IsLocalProartinianAlgebra 𝒪 _ A _ (maximalIdeal A).adicTopology _ := by

  letI : TopologicalSpace A := (maximalIdeal A).adicTopology
  haveI : IsTopologicalRing A := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
  haveI : IsLocalRing.IsAdicTopology A := ⟨rfl⟩

  haveI : Finite (ResidueField A) := by
    have hsurj : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap 𝒪 A)) := by
      intro y
      obtain ⟨o, ho⟩ := hres y
      exact ⟨IsLocalRing.residue 𝒪 o, ho⟩
    exact Finite.of_surjective _ hsurj

  haveI : CompactSpace A := IsLocalRing.compactSpace_of_finite_residueField
  haveI : IsProartinian A := inferInstance

  haveI : IsResidueAlgebra 𝒪 A := ⟨by
    rwa [IsScalarTower.algebraMap_eq 𝒪 A (ResidueField A), ResidueField.algebraMap_eq, RingHom.coe_comp]⟩
  exact Deformation.IsLocalProartinianAlgebra.mk

import Definitions.Def_Deformations_ProartinianCat
import P2M.Util
namespace P2MW.S_IsLocalRing_isLocalProartinianAlgebra_adicTopology

universe u

open IsLocalRing Deformation

theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
    (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap 𝒪 R))) :
    letI : TopologicalSpace R := (maximalIdeal R).adicTopology
    IsLocalProartinianAlgebra 𝒪 R := by
  letI : TopologicalSpace R := (maximalIdeal R).adicTopology
  letI : IsTopologicalRing R := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
  letI : IsAdicTopology R := ⟨rfl⟩
  haveI : Finite (ResidueField R) := by
    refine Finite.of_surjective (ResidueField.map (algebraMap 𝒪 R)) fun y => ?_
    obtain ⟨c, hc⟩ := hres y
    exact ⟨residue 𝒪 c, by rw [ResidueField.map_residue]; exact hc⟩
  letI : CompactSpace R := compactSpace_of_finite_residueField
  haveI : IsResidueAlgebra 𝒪 R := ⟨hres⟩
  exact ⟨⟩

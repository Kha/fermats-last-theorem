import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Algebra.Hom
import P2M.Util
namespace P2MW.S_IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map

set_option autoImplicit false

open IsLocalRing

namespace CohL2
namespace Residue

theorem map_mem_maximalIdeal {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L] (πT : L →ₐ[𝒪] 𝒪)
    {z : L} (hz : z ∈ maximalIdeal L) : πT z ∈ maximalIdeal 𝒪 := by
  by_contra hu
  have hunit : IsUnit (πT z) := of_not_not fun h => hu ((mem_maximalIdeal _).mpr h)

  have hk : πT (algebraMap 𝒪 L (πT z) - z) = 0 := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hv : IsUnit (algebraMap 𝒪 L (πT z) - z) := by
    by_contra hnu
    have hm : algebraMap 𝒪 L (πT z) - z ∈ maximalIdeal L := (mem_maximalIdeal _).mpr hnu
    have : algebraMap 𝒪 L (πT z) ∈ maximalIdeal L := by
      have := Ideal.add_mem _ hm hz
      rwa [sub_add_cancel] at this
    exact (mem_maximalIdeal _).mp this (hunit.map _)
  have h1 : IsUnit (πT (algebraMap 𝒪 L (πT z) - z)) := hv.map πT
  rw [hk] at h1
  exact not_isUnit_zero h1

theorem residue_point_eq {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L] [IsLocalHom (algebraMap 𝒪 L)]
    (πT : L →ₐ[𝒪] 𝒪) (z : L) (x : ResidueField 𝒪)
    (hz : residue L z = ResidueField.map (algebraMap 𝒪 L) x) :
    residue 𝒪 (πT z) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x

  have h1 : residue L z = residue L (algebraMap 𝒪 L a) := by
    rw [hz]; rfl
  have h2 : z - algebraMap 𝒪 L a ∈ maximalIdeal L := by
    rw [← Ideal.Quotient.eq]; exact h1
  have h3 : πT z - a ∈ maximalIdeal 𝒪 := by
    have := map_mem_maximalIdeal πT h2
    rwa [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at this
  show Ideal.Quotient.mk _ (πT z) = Ideal.Quotient.mk _ a
  exact (Ideal.Quotient.eq).mpr h3

end CohL2.Residue

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L] [IsLocalHom (algebraMap 𝒪 L)]
    (πT : L →ₐ[𝒪] 𝒪) (z : L) (x : IsLocalRing.ResidueField 𝒪)
    (hz : IsLocalRing.residue L z = IsLocalRing.ResidueField.map (algebraMap 𝒪 L) x) :
    IsLocalRing.residue 𝒪 (πT z) = x :=
  CohL2.Residue.residue_point_eq πT z x hz

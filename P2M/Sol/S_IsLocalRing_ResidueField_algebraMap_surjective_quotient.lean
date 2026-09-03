import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import P2M.Util
namespace P2MW.S_IsLocalRing_ResidueField_algebraMap_surjective_quotient

open IsLocalRing

namespace LCMazurS10LTRES

variable {A : Type*} [CommRing A] [IsLocalRing A]

omit [IsLocalRing A] in
theorem nontrivial_quotient_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : Nontrivial (A ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr hI

theorem isLocalRing_quotient_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : IsLocalRing (A ⧸ I) :=
  haveI := nontrivial_quotient_of_ne_top hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isLocalHom_mk_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) : IsLocalHom (Ideal.Quotient.mk I) :=
  haveI := nontrivial_quotient_of_ne_top hI
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

theorem map_maximalIdeal_mk_of_ne_top {I : Ideal A} (hI : I ≠ ⊤) [IsLocalRing (A ⧸ I)] :
    (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
  haveI := isLocalHom_mk_of_ne_top hI
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (le_maximalIdeal hI), mem_maximalIdeal,
    mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

end LCMazurS10LTRES

open LCMazurS10LTRES in
theorem solution
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (I : Ideal A) [IsLocalRing (A ⧸ I)]
    (h : Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField A))) :
    Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField (A ⧸ I))) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨o, ho⟩ := h (IsLocalRing.residue A a)
  refine ⟨o, ?_⟩
  change IsLocalRing.residue (A ⧸ I) (Ideal.Quotient.mk I (algebraMap 𝒪 A o)) =
    IsLocalRing.residue (A ⧸ I) (Ideal.Quotient.mk I a)
  change IsLocalRing.residue A (algebraMap 𝒪 A o) = IsLocalRing.residue A a at ho
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at ho ⊢
  rw [← map_sub, ← map_maximalIdeal_mk_of_ne_top hI]
  exact Ideal.mem_map_of_mem _ ho

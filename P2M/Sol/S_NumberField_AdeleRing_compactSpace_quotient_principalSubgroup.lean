import Definitions.Def_NumberField_AdelicBox
import P2M.Util
namespace P2MW.S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup

set_option Elab.async false
set_option autoImplicit false

open NumberField NumberField.AdelicBox

theorem solution (F : Type) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  rw [← isCompact_univ_iff]

  have hcont : Continuous
      (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) :=
    continuous_quot_mk
  have hsurj : (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) '' C
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y

    obtain ⟨x, rfl⟩ := Quot.exists_rep y
    obtain ⟨k, hk, -⟩ := existsUnique_algebraMap_add_mem_adelicBox F x
    refine ⟨algebraMap F (AdeleRing (𝓞 F) F) k + x, hsub hk, ?_⟩

    refine (QuotientAddGroup.eq (s := AdeleRing.principalSubgroup (𝓞 F) F)).mpr ?_
    refine ⟨-k, ?_⟩
    simp only [map_neg]
    abel
  rw [← hsurj]
  exact hC.image hcont

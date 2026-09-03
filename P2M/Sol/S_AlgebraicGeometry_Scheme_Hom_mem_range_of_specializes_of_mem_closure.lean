import Mathlib
import Theorems.Thm_IrreducibleSpace_genericPoint_mem_range_of_denseRange
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_mem_range_of_specializes_of_mem_closure

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem solution
    {Γ G : Scheme.{u}} (π : Γ ⟶ G) [QuasiCompact π] [LocallyOfFiniteType π] [IsLocallyNoetherian G]
    (S : Set G) (hS : IsClosed S) (η : G) (hηS : η ∈ S) (hirr : ∀ x ∈ S, η ⤳ x)
    (D : Set G) (hDS : D ⊆ S) (hDη : η ∈ closure D) (hDπ : D ⊆ Set.range π.base) :
    η ∈ Set.range π.base := by
  classical

  obtain ⟨W, hW, hηW, -⟩ := exists_isAffineOpen_mem_and_subset (X := G) (x := η) (U := ⊤) trivial
  haveI : IsLocallyNoetherian Γ := LocallyOfFiniteType.isLocallyNoetherian π

  have hOc : IsCompact ((π ⁻¹ᵁ W : Γ.Opens) : Set Γ) := π.isCompact_preimage hW.isCompact
  haveI : CompactSpace (π ⁻¹ᵁ W) := isCompact_iff_compactSpace.mp hOc
  haveI : IsNoetherian (π ⁻¹ᵁ W) := {}
  haveI hNO : NoetherianSpace ((π ⁻¹ᵁ W : Γ.Opens) : Set Γ) :=
    (inferInstance : NoetherianSpace (π ⁻¹ᵁ W))

  set Ys : Set G := (W : Set G) ∩ S
  set Xs : Set Γ := ((π ⁻¹ᵁ W : Γ.Opens) : Set Γ) ∩ π.base ⁻¹' S
  haveI : NoetherianSpace Xs := NoetherianSpace.inter_of_left _ _
  haveI : QuasiSober ((π ⁻¹ᵁ W : Γ.Opens) : Set Γ) :=
    (π ⁻¹ᵁ W).2.isOpenEmbedding_subtypeVal.quasiSober
  haveI : QuasiSober Xs :=
    QuasiSober.inter_of_isClosed_of_quasiSober_left _ (hS.preimage π.continuous)
  haveI : QuasiSober (W : Set G) := W.2.isOpenEmbedding_subtypeVal.quasiSober
  haveI : QuasiSober Ys := QuasiSober.inter_of_isClosed_of_quasiSober_left _ hS

  let ηY : Ys := ⟨η, hηW, hηS⟩
  have hgenY : IsGenericPoint ηY (Set.univ : Set Ys) := by
    rw [isGenericPoint_def, Set.eq_univ_iff_forall]
    intro y
    rw [← specializes_iff_mem_closure, ← Topology.IsInducing.subtypeVal.specializes_iff]
    exact hirr y.1 y.2.2
  haveI : IrreducibleSpace Ys := by
    have hpre : IsPreirreducible (Set.univ : Set Ys) := by
      rw [← hgenY.def]
      exact isPreirreducible_singleton.closure
    exact @IrreducibleSpace.mk _ _ ⟨hpre⟩ ⟨ηY⟩
  have hgp : genericPoint Ys = ηY := (genericPoint_spec Ys).eq hgenY

  let f : Xs → Ys := fun x => ⟨π.base x.1, x.2.1, x.2.2⟩
  have hf : Continuous f := (π.continuous.comp continuous_subtype_val).subtype_mk _

  have hEsub : (Subtype.val ⁻¹' D : Set Ys) ⊆ Set.range f := by
    rintro ⟨d, hdW, hdS⟩ hdD
    obtain ⟨γ, hγ⟩ := hDπ hdD
    refine ⟨⟨γ, ?_, ?_⟩, Subtype.ext hγ⟩
    · show π.base γ ∈ (W : Set G)
      rw [hγ]; exact hdW
    · show π.base γ ∈ S
      rw [hγ]; exact hdS
  have hηE : ηY ∈ closure (Subtype.val ⁻¹' D : Set Ys) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
    have h1 : η ∈ closure ((W : Set G) ∩ D) := W.2.inter_closure ⟨hηW, hDη⟩
    refine closure_mono ?_ h1
    rintro d ⟨hdW, hdD⟩
    exact ⟨⟨d, hdW, hDS hdD⟩, hdD, rfl⟩
  have hd : DenseRange f := by
    intro y
    have hy : y ∈ closure ({ηY} : Set Ys) := by rw [hgenY.def]; trivial
    have hηr : ηY ∈ closure (Set.range f) := closure_mono hEsub hηE
    exact closure_minimal (Set.singleton_subset_iff.mpr hηr) isClosed_closure hy

  have hmem := IrreducibleSpace.genericPoint_mem_range_of_denseRange hf hd
  rw [hgp] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x.1, congrArg Subtype.val hx⟩

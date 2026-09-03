import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import P2M.Util
namespace P2MW.S_Rep_relationSeqInt_shortExact

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open CategoryTheory

namespace Rep p2m_export "Rep" "of epi_iff_surjective mono_iff_injective hV2 freeCover relationModule relationModule.ι_hom_apply freeCover_hom_apply_ι relationModuleInt relationModuleInt.ι_hom_apply relationSeqInt" end Rep
p2m_open_scoped "Rep" in

theorem Rep.shortExact_of_hom {k G : Type} [CommRing k] [Group G] {S : ShortComplex (Rep k G)}
    (hf : Function.Injective S.f.hom) (hg : Function.Surjective S.g.hom)
    (hfg : ∀ y : S.X₂, S.g.hom y = 0 ↔ y ∈ Set.range S.f.hom) : S.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 hf) ((Rep.epi_iff_surjective _).2 hg)
  refine Functor.reflects_exact_of_faithful (forget₂ (Rep k G) (ModuleCat k)) _ ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  intro y
  exact hfg y

theorem solution {G : Type} [Group G] (B : Rep ℤ G) :
    (Rep.relationSeqInt B).ShortExact := by
  refine Rep.shortExact_of_hom ?_ ?_ ?_
  · intro x y hxy
    rw [Rep.relationModuleInt.ι_hom_apply, Rep.relationModuleInt.ι_hom_apply,
      Rep.relationModule.ι_hom_apply, Rep.relationModule.ι_hom_apply] at hxy
    exact Subtype.ext hxy
  · intro b
    refine ⟨Finsupp.single b (MonoidAlgebra.single 1 1), ?_⟩
    simp only [Rep.freeCover]
    simp
    exact (int_smul_eq_zsmul B.hV2 1 b).trans (one_zsmul b)
  · intro y
    constructor
    · intro hy
      exact ⟨(show Rep.relationModuleInt B from (⟨y, hy⟩ : Rep.relationModule B)), rfl⟩
    · rintro ⟨x, rfl⟩
      exact Rep.freeCover_hom_apply_ι B (show Rep.relationModule B from x)

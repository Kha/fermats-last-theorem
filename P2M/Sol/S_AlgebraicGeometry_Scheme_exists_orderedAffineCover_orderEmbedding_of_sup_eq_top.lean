import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_orderedAffineCover_orderEmbedding_of_sup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace KGSOL

theorem main
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover) :
    ∃ (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι),
      (∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) ∧ (∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a) ∧
      (∀ b a, eV b < eU a) ∧ ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU := by
  classical

  let chart : 𝔙.ι ⊕ 𝔘.ι → X.Opens :=
    Sum.elim (fun b => V.ι ''ᵁ 𝔙.U b) (fun a => U.ι ''ᵁ 𝔘.U a)
  have hchart : ∀ s, IsAffineOpen (chart s) := by
    rintro (b | a)
    · exact (𝔙.isAffineOpen b).image_of_isOpenImmersion V.ι
    · exact (𝔘.isAffineOpen a).image_of_isOpenImmersion U.ι
  have hsup : ⨆ s, chart s = ⊤ := by
    rw [iSup_sum]
    change (⨆ b, V.ι ''ᵁ 𝔙.U b) ⊔ (⨆ a, U.ι ''ᵁ 𝔘.U a) = ⊤
    rw [← Scheme.Hom.image_iSup, ← Scheme.Hom.image_iSup, 𝔙.iSup_eq_top, 𝔘.iSup_eq_top,
      Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, sup_comm, hUV]
  let 𝔛' : X.OrderedAffineCover :=
    { ι := 𝔙.ι ⊕ₗ 𝔘.ι
      U := fun i => chart (ofLex i)
      isAffineOpen := fun i => hchart (ofLex i)
      iSup_eq_top := hsup }
  refine ⟨𝔛', OrderEmbedding.ofStrictMono (fun b => toLex (Sum.inl b)) Sum.Lex.inl_strictMono,
    OrderEmbedding.ofStrictMono (fun a => toLex (Sum.inr a)) Sum.Lex.inr_strictMono,
    fun b => rfl, fun a => rfl, fun b a => Sum.Lex.inl_lt_inr b a, ?_⟩
  intro j
  obtain ⟨s, rfl⟩ := toLex.surjective j
  rcases s with b | a
  · exact Or.inl ⟨b, rfl⟩
  · exact Or.inr ⟨a, rfl⟩

end KGSOL

theorem solution
    {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (𝔙 : (V : Scheme.{u}).OrderedAffineCover) (𝔘 : (U : Scheme.{u}).OrderedAffineCover) :
    ∃ (𝔛' : X.OrderedAffineCover) (eV : 𝔙.ι ↪o 𝔛'.ι) (eU : 𝔘.ι ↪o 𝔛'.ι),
      (∀ b, 𝔛'.U (eV b) = V.ι ''ᵁ 𝔙.U b) ∧ (∀ a, 𝔛'.U (eU a) = U.ι ''ᵁ 𝔘.U a) ∧
      (∀ b a, eV b < eU a) ∧ ∀ j, j ∈ Set.range eV ∨ j ∈ Set.range eU :=
  KGSOL.main U V hUV 𝔙 𝔘

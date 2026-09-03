import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_PartialAction_closure_image_preimage_closure_eq_closure_singleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Topology

universe u

theorem solution
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)
    (Z : Set ↥P) (ζ : ↥(pullback f p)) (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure Z) :
    closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure Z)) =
      closure ({a.hom.base ⟨ζ, hζ⟩} : Set ↥P) := by

  have himg : (a.dom.ι : ↥(a.dom : Scheme.{u}) → ↥(pullback f p)) '' {⟨ζ, hζ⟩} = {ζ} := by
    ext z; simp [Scheme.Opens.ι_apply]
  have hpre : (a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure Z =
      closure ({⟨ζ, hζ⟩} : Set ↥(a.dom : Scheme.{u})) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← hζcl,
      a.dom.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
    congr 2
    exact himg.symm
  rw [hpre]
  apply le_antisymm
  · rw [← closure_closure (s := ({a.hom.base _} : Set ↥P))]
    refine closure_mono ?_
    have h__af := (image_closure_subset_closure_image a.hom.base.hom.continuous
        (s := ({(⟨ζ, hζ⟩ : ↥(a.dom : Scheme.{u}))} : Set _)))
    simp only [Set.image_singleton] at h__af
    exact h__af
  · exact closure_mono (Set.singleton_subset_iff.2 ⟨_, subset_closure rfl, rfl⟩)

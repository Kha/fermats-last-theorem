import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (s s' : T ⟶ X) (h : s ≫ f = s' ≫ f) (t₀ : ↥T) (ht₀ : ∀ t : ↥T, t ⤳ t₀)
    (hΔ : (pullback.lift s s' h).base t₀ ∈ Set.range (pullback.diagonal f).base) :
    s = s' := by

  have hrange : Set.range (pullback.lift s s' h).base ⊆ Set.range (pullback.diagonal f).base := by
    rintro _ ⟨t, rfl⟩
    exact ((ht₀ t).map (pullback.lift s s' h).continuous).mem_open
      (pullback.diagonal f).isOpenEmbedding.isOpen_range hΔ

  let l := IsOpenImmersion.lift (pullback.diagonal f) (pullback.lift s s' h) hrange
  have hl : l ≫ pullback.diagonal f = pullback.lift s s' h := IsOpenImmersion.lift_fac _ _ _
  have hs : s = l := by
    have := congrArg (· ≫ pullback.fst f f) hl
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at this
    exact this.symm
  have hs' : s' = l := by
    have := congrArg (· ≫ pullback.snd f f) hl
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] at this
    exact this.symm
  rw [hs, hs']

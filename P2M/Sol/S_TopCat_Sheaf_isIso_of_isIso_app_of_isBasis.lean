import Mathlib
import P2M.Util
namespace P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis

universe u v w u'

open CategoryTheory Opposite TopologicalSpace

theorem solution {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G : TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ := by
  haveI := TopCat.Opens.coverDense_inducedFunctor hB
  haveI : IsIso (Functor.whiskerLeft (inducedFunctor B).op φ.1) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro i
    exact h i.unop
  exact Functor.IsCoverDense.iso_of_restrict_iso φ this

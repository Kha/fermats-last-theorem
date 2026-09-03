import Mathlib
import P2M.Util
namespace P2MW.S_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem solution {C : Type w} [Category.{v} C] {X X' S T : C}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [HasPullback f t] [HasPullback f' t] :
    IsPullback (pullback.fst f' t)
      (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp]))
      π (pullback.fst f t) := by
  have big : IsPullback (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ])
      (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd f t) (pullback.fst f' t) t (π ≫ f) := by
    rw [pullback.lift_snd, Category.comp_id, hπ]
    exact (IsPullback.of_hasPullback f' t).flip
  exact (IsPullback.of_right big (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f t).flip).flip

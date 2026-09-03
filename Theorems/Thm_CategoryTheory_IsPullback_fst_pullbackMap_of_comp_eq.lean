import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq {C : Type w} [Category.{v} C] {X X' S T : C}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [HasPullback f t] [HasPullback f' t] :
    IsPullback (pullback.fst f' t)
      (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ]) (by rw [Category.comp_id, Category.id_comp]))
      π (pullback.fst f t) := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq.solution

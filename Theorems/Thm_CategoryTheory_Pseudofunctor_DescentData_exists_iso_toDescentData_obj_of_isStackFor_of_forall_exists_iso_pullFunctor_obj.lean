import Mathlib
import P2M.Util
import P2M.Sol.S_CategoryTheory_Pseudofunctor_DescentData_exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj

universe t v' u' v u

open CategoryTheory CategoryTheory.Limits Opposite

theorem CategoryTheory.Pseudofunctor.DescentData.exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (P : ∀ ⦃Z : C⦄, F.obj (.mk (op Z)) → Prop)
    (hP : ∀ ⦃Z Z' : C⦄ (g : Z' ⟶ Z) (M : F.obj (.mk (op Z))), P M → P ((F.map g.op.toLoc).toFunctor.obj M))
    (hP' : ∀ ⦃Z : C⦄ (M N : F.obj (.mk (op Z))), Nonempty (M ≅ N) → P M → P N)
    {S X : C} (f : X ⟶ S) {ι : Type t} {U : ι → C} (u : ∀ i, U i ⟶ S)
    (hS : F.IsStackFor (Presieve.ofArrows U u))
    (hZ : ∀ ⦃Z : C⦄ (z : Z ⟶ S),
      F.IsPrestackFor (Presieve.ofArrows (fun i => pullback z (u i)) (fun i => pullback.fst z (u i))))
    (hf : ∀ ⦃Z : C⦄ (z : Z ⟶ S) (M N : F.obj (.mk (op Z))), P M → P N →
      Function.Bijective ((F.toDescentData (fun _ : Unit => pullback.snd f z)).map : (M ⟶ N) → _))
    (D : F.DescentData (fun _ : Unit => f))
    (hD : ∀ i, ∃ L : F.obj (.mk (op (U i))), P L ∧
      Nonempty ((F.toDescentData (fun _ : Unit => pullback.snd f (u i))).obj L ≅
        (Pseudofunctor.DescentData.pullFunctor F (f := fun _ : Unit => f) (p := u i)
          (f' := fun _ : Unit => pullback.snd f (u i)) (α := fun j => j) (p' := fun _ => pullback.fst f (u i))
          (fun _ => pullback.condition)).obj D)) :
    ∃ L : F.obj (.mk (op S)), (∀ i, P ((F.map (u i).op.toLoc).toFunctor.obj L)) ∧
      Nonempty ((F.toDescentData (fun _ : Unit => f)).obj L ≅ D) := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Pseudofunctor_DescentData_exists_iso_toDescentData_obj_of_isStackFor_of_forall_exists_iso_pullFunctor_obj.solution

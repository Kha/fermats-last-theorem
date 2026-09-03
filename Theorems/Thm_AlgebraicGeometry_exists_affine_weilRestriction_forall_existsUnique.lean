import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.exists_affine_weilRestriction_forall_existsUnique
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R']
    (H : Type u) [CommRing H] [Algebra R' H] [Algebra.FiniteType R' H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra R W), Algebra.FiniteType R W ∧
      ∃ υ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R W))) ⟶
          Spec (CommRingCat.of H),
        υ ≫ Spec.map (CommRingCat.ofHom (algebraMap R' H)) = pullback.fst _ _ ∧
        ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R))
          (y : SchemeHomOver (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
            (Spec.map (CommRingCat.ofHom (algebraMap R' H)))),
          ∃! x : SchemeHomOver t (Spec.map (CommRingCat.ofHom (algebraMap R W))),
            pullback.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t)
                (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R'))) t ≫ x.1)
                (by rw [Category.assoc, x.2, pullback.condition]) ≫ υ = y.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_affine_weilRestriction_forall_existsUnique.solution

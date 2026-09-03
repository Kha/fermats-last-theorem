import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.etale_of_forall_dualNumber_eq_comp
    {κ : Type u} [Field κ] [IsAlgClosed κ] {K : Scheme.{u}} (fK : K ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fK]
    (h : ∀ v : Spec (CommRingCat.of (DualNumber κ)) ⟶ K,
      v ≫ fK = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) →
      v = Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ))) ≫
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ v) :
    Etale fK := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_etale_of_forall_dualNumber_eq_comp.solution

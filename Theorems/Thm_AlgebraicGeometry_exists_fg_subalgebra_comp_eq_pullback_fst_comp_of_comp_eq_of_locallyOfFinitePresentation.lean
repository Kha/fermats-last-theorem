import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
    {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A) (hB : B.FG)
    {X W V : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ↥B)) [LocallyOfFiniteType f]
    (w : W ⟶ X) [QuasiCompact (w ≫ f)] [QuasiSeparated (w ≫ f)]
    (v : V ⟶ X) [LocallyOfFinitePresentation (v ≫ f)]
    (a : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ⟶ V)
    (ha : a ≫ v = pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ≫ w) :
    ∃ (T : Subalgebra A₀ A) (_ : T.FG) (hle : B ≤ T)
      (aT : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ⟶ V),
      aT ≫ v = pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ≫ w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation.solution

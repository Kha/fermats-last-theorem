import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k)) (D : P.Opens)
      (τ : (D : Scheme.{u}) ⟶ X) (V : X.Opens) (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u})),
      IsProper p ∧ IsIntegral P ∧ (∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y)) ∧
      IsProper τ ∧ τ ≫ f = D.ι ≫ p ∧
      Nonempty (V : Scheme.{u}) ∧ IsOpenImmersion ι ∧ ι ≫ τ = V.ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isProper_isIntegrallyClosed_stalk_isOpenImmersion_comp_eq_of_isSeparated.solution

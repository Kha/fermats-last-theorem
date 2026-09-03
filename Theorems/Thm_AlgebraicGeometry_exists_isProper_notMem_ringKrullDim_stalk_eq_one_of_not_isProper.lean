import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
attribute [-instance] AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hX : ¬ IsProper f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsProper p] [IsIntegral P]
    (hn : ∀ y : P, IsIntegrallyClosed (P.presheaf.stalk y))
    (D : P.Opens) (τ : (D : Scheme.{u}) ⟶ X) [IsProper τ] (hτ : τ ≫ f = D.ι ≫ p)
    (V : X.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ (D : Scheme.{u}))
    [IsOpenImmersion ι] (hτι : ι ≫ τ = V.ι) :
    ∃ (P' : Scheme.{u}) (π : P' ⟶ P) (V' : X.Opens)
      (ι' : (V' : Scheme.{u}) ⟶ (π ⁻¹ᵁ D : Scheme.{u})),
      IsIntegral P' ∧ (∀ y : P', IsIntegrallyClosed (P'.presheaf.stalk y)) ∧ IsProper π ∧
      Nonempty (V' : Scheme.{u}) ∧ IsOpenImmersion ι' ∧ ι' ≫ (π ∣_ D) ≫ τ = V'.ι ∧
      ∃ w : P', w ∉ (π ⁻¹ᵁ D : Set P') ∧ ringKrullDim (P'.presheaf.stalk w) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isProper_notMem_ringKrullDim_stalk_eq_one_of_not_isProper.solution

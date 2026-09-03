import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType
attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {ι : Type v} [Finite ι] {X₁ X₂ : ι → Scheme.{u}}
    (f₁ : ∀ i, X₁ i ⟶ Spec (CommRingCat.of A₀)) (f₂ : ∀ i, X₂ i ⟶ Spec (CommRingCat.of A₀))
    [∀ i, QuasiCompact (f₁ i)] [∀ i, LocallyOfFiniteType (f₂ i)]
    (a b : ∀ i, X₁ i ⟶ X₂ i) (ha : ∀ i, a i ≫ f₂ i = f₁ i) (hb : ∀ i, b i ≫ f₂ i = f₁ i)
    (hab : ∀ i, pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ a i =
      pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≫ b i) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ i, pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ a i =
        pullback.fst (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≫ b i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_forall_pullback_fst_comp_eq_of_locallyOfFiniteType.solution

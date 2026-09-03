import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {ι : Type v} [Finite ι] {X₁ X₂ : ι → Scheme.{u}}
    (f₁ : ∀ i, X₁ i ⟶ Spec (CommRingCat.of A₀)) (f₂ : ∀ i, X₂ i ⟶ Spec (CommRingCat.of A₀))
    [∀ i, QuasiCompact (f₁ i)] [∀ i, QuasiSeparated (f₁ i)] [∀ i, LocallyOfFinitePresentation (f₂ i)]
    (g : ∀ i, pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
      pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (hg : ∀ i, g i ≫ pullback.snd (f₂ i) _ = pullback.snd (f₁ i) _) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ g₀ : ∀ i, pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        (∀ i, g₀ i ≫ pullback.snd (f₂ i) _ = pullback.snd (f₁ i) _) ∧
        ∀ (i : ι)
          (q₁ : pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback (f₁ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
          (q₂ : pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback (f₂ i) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))),
          q₁ ≫ pullback.fst (f₁ i) _ = pullback.fst (f₁ i) _ →
          q₁ ≫ pullback.snd (f₁ i) _ = pullback.snd (f₁ i) _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₂ ≫ pullback.fst (f₂ i) _ = pullback.fst (f₂ i) _ →
          q₂ ≫ pullback.snd (f₂ i) _ = pullback.snd (f₂ i) _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₁ ≫ g₀ i = g i ≫ q₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_forall_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation.solution

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType open NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₁]
    [QuasiCompact f₂] [QuasiSeparated f₂] [LocallyOfFinitePresentation f₂]
    (L₁ : RelativeGroupLaw A₀ f₁) (L₂ : RelativeGroupLaw A₀ f₂)
    (e : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≅
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (he : e.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    (hemul : ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of A))
        (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))),
      ((L₁.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t x y).1 ≫ e.hom =
        ((L₂.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1)
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ (B : Type u) [CommRing B] (φ : ↥T →+* B) (χ : A₀ →+* B), φ.comp (algebraMap A₀ ↥T) = χ →
        ∃ (e' : pullback f₁ (Spec.map (CommRingCat.ofHom χ)) ≅ pullback f₂ (Spec.map (CommRingCat.ofHom χ)))
          (he' : e'.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _),
          ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of B))
            (x y : SchemeHomOver t (pullback.snd f₁ (Spec.map (CommRingCat.ofHom χ)))),
            ((L₁.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t x y).1 ≫ e'.hom =
              ((L₂.baseChange (Spec.map (CommRingCat.ofHom χ))).mul t
                ⟨x.1 ≫ e'.hom, by rw [Category.assoc, he', x.2]⟩ ⟨y.1 ≫ e'.hom, by rw [Category.assoc, he', y.2]⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_forall_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.solution

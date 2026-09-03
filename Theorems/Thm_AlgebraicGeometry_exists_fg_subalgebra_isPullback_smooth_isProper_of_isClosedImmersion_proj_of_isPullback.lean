import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
theorem AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (S₁ : Subalgebra ℤ S) (hS₁ : S₁.FG) (Z₁ : Scheme.{u}) (f₁ : Z₁ ⟶ Spec (CommRingCat.of ↥S₁)) (g₁ : Z ⟶ Z₁)
    (hg₁ : IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ S))))
    (hsm₁ : Smooth f₁) (hpr₁ : IsProper f₁) (hgc₁ : GeometricallyConnected f₁) :
    ∃ (S₀ : Subalgebra ℤ S) (_ : S₀.FG) (Z₀ : Scheme.{u}) (f₀ : Z₀ ⟶ Spec (CommRingCat.of ↥S₀)) (g : Z ⟶ Z₀),
      IsPullback g f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S))) ∧
      Smooth f₀ ∧ IsProper f₀ ∧
      (∃ (N₀ : ℕ) (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N₀ + 1)) ↥S₀)),
        IsClosedImmersion ι₀ ∧ ι₀ ≫ ProjSpace.π ↥S₀ N₀ = f₀) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x₀ : ↥S₀ →+* k),
        ConnectedSpace ↥(pullback f₀ (Spec.map (CommRingCat.ofHom x₀)))) ∧
      ∃ ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥S₀))) f₀,
        ε.1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S)) ≫ ε₀.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback.solution

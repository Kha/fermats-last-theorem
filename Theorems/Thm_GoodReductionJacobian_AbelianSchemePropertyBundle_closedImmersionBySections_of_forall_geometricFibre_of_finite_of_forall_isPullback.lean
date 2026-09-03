import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation open AlgebraicGeometry hiding isClosedImmersion_of_universallyClosed_of_universallyInjective_of_formallyUnramified

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      Scheme.Modules.ClosedImmersionBySections
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M)
        (pullback.snd f (Spec.map (CommRingCat.ofHom sk))))
    (hfg : letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
      Module.Finite S Γ(M, ⊤) ∧ Module.Projective S Γ(M, ⊤))
    (hbc : ∀ (S' : Type) [CommRing S'] (φ : S →+* S')
        (A' : Scheme.{0}) (f' : A' ⟶ Spec (CommRingCat.of S')) (gA : A' ⟶ A)
        (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ))),
        letI : Module S Γ(M, ⊤) := Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom
        letI : Module S' Γ((Scheme.Modules.pullback gA).obj M, gA ⁻¹ᵁ ⊤) :=
          Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (gA ⁻¹ᵁ ⊤) le_top).hom
        letI : Algebra S S' := φ.toAlgebra
        ∃ e : S' ⊗[S] Γ(M, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback gA).obj M, gA ⁻¹ᵁ ⊤),
          ∀ (s' : S') (τ : Γ(M, ⊤)), e (s' ⊗ₜ[S] τ) = s' • Scheme.Modules.pullbackLocalSection gA τ) :
    Scheme.Modules.ClosedImmersionBySections M f := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_closedImmersionBySections_of_forall_geometricFibre_of_finite_of_forall_isPullback.solution

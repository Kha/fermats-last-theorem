import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_cocycle_of_rigidifiedIso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Polarisation.cocycle_of_rigidifiedIso
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    {A A' A'' X₃ : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [IsSeparated f]
    (hH0 : ∀ (T : Type u) [CommRing T] [Algebra R T],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R T)) ⊤
      Function.Bijective (algebraMap T Γ(pullback f (Scheme.TwoAffineOpenCover.specMap R T), ⊤)))
    (e : Spec (CommRingCat.of R) ⟶ A) (he : e ≫ f = 𝟙 _)
    (f' : A' ⟶ Spec (CommRingCat.of R')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (f'' : A'' ⟶ Spec (CommRingCat.of (R' ⊗[R] R'))) (a₁ a₂ : A'' ⟶ A')
    (ha₁ : IsPullback a₁ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f'
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)))
    (hga : a₁ ≫ g = a₂ ≫ g)

    (e' : Spec (CommRingCat.of R') ⟶ A') (he'g : e' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ e)
    (he'f : e' ≫ f' = 𝟙 _)
    (e'' : Spec (CommRingCat.of (R' ⊗[R] R')) ⟶ A'')
    (he''a₁ : e'' ≫ a₁ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom) ≫ e')
    (he''a₂ : e'' ≫ a₂ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom) ≫ e')
    (he''f : e'' ≫ f'' = 𝟙 _)

    (L₁ : A'.Modules) (hL₁ : Scheme.Modules.IsInvertible L₁)
    (α : (Scheme.Modules.pullback e').obj L₁ ≅ SheafOfModules.unit (Spec (CommRingCat.of R')).ringCatSheaf)
    (ψ : (Scheme.Modules.pullback a₁).obj L₁ ≅ (Scheme.Modules.pullback a₂).obj L₁)
    (hψ : (Scheme.Modules.pullback e'').mapIso ψ ≪≫
        ((Scheme.Modules.pullbackComp e'' a₂).app L₁ ≪≫ (Scheme.Modules.pullbackCongr he''a₂).app L₁ ≪≫
          ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)) e').app L₁).symm ≪≫
          (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom))).mapIso α ≪≫
          Scheme.Modules.pullbackUnitIso _) =
      ((Scheme.Modules.pullbackComp e'' a₁).app L₁ ≪≫ (Scheme.Modules.pullbackCongr he''a₁).app L₁ ≪≫
          ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)) e').app L₁).symm ≪≫
          (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom))).mapIso α ≪≫
          Scheme.Modules.pullbackUnitIso _))

    (t₃ : X₃ ⟶ Spec (CommRingCat.of (R' ⊗[R] (R' ⊗[R] R')))) (p₃ : X₃ ⟶ A)
    (hX₃ : IsPullback p₃ t₃ f
      (Spec.map (CommRingCat.ofHom (S := (R' ⊗[R] (R' ⊗[R] R'))) (algebraMap R (R' ⊗[R] (R' ⊗[R] R'))))))
    (b₁₂ b₁₃ b₂₃ : X₃ ⟶ A'')
    (hb₁₂g : b₁₂ ≫ a₁ ≫ g = p₃) (hb₁₃g : b₁₃ ≫ a₁ ≫ g = p₃) (hb₂₃g : b₂₃ ≫ a₁ ≫ g = p₃)
    (hb₁₂f : b₁₂ ≫ f'' = t₃ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R')).toRingHom))
    (hb₁₃f : b₁₃ ≫ f'' = t₃ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R') (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R')).toRingHom))
    (hb₂₃f : b₂₃ ≫ f'' = t₃ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : R' ⊗[R] R' →ₐ[R] R' ⊗[R] (R' ⊗[R] R')).toRingHom))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂) :
    ((Scheme.Modules.pullbackCongr h₁).app L₁).symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L₁).symm ≪≫
        (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L₁) ≪≫
        ((Scheme.Modules.pullbackCongr h₂).app L₁) ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L₁).symm ≪≫
        (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L₁) ≪≫
        ((Scheme.Modules.pullbackCongr h₃).app L₁).symm
      = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L₁).symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫
        ((Scheme.Modules.pullbackComp b₁₃ a₂).app L₁) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_cocycle_of_rigidifiedIso.solution

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) :
    IsFibreReading V ι f fk i U W hW 0 0 ∧
    (∀ (δ δ' : Γ(X, U)) (w w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W),
        IsFibreReading V ι f fk i U W hW δ w → IsFibreReading V ι f fk i U W hW δ' w' →
          IsFibreReading V ι f fk i U W hW (δ + δ') (w + w')) ∧
    (∀ (δ s : Γ(X, U)) (w w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W),
        IsFibreReading V ι f fk i U W hW δ w →
          (∀ ξ : Module.Dual k V, w' ξ =
            (show Γ(Xk, W) from (OModulePresheaf.unit fk).res hW
              (show (OModulePresheaf.unit fk).obj (i ⁻¹ᵁ U) from (i.app U).hom s)) • w ξ) →
          IsFibreReading V ι f fk i U W hW (s * δ) w') ∧
    (∀ (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W),
        IsFibreReading V ι f fk i U W hW δ w → IsFibreReading V ι f fk i U W hW (-δ) (-w)) ∧
    (∀ (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
        (U' : X.Opens) (W' : Xk.Opens) (hU' : U' ≤ U) (hW'W : W' ≤ W) (hW' : W' ≤ i ⁻¹ᵁ U'),
        IsFibreReading V ι f fk i U W hW δ w →
          IsFibreReading V ι f fk i U' W' hW' ((X.presheaf.map (homOfLE hU').op).hom δ)
            (((OModulePresheaf.unit fk).res hW'W).comp w)) ∧
    (∀ δ : Γ(X, U), (letI := algebraOfHom f U
        δ ∈ Ideal.map (algebraMap B₁ Γ(X, U)) (LinearMap.range ι)) →
        ∃ w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W, IsFibreReading V ι f fk i U W hW δ w) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading.solution

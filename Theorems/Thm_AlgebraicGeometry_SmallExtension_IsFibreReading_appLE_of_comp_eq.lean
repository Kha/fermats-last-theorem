import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.SmallExtension Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) (i' : Xk' ⟶ X')
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U)
    (U' : X'.Opens) (hU' : U' ≤ h ⁻¹ᵁ U) (W' : Xk'.Opens) (hW' : W' ≤ i' ⁻¹ᵁ U') (hWk : W' ≤ hk ⁻¹ᵁ W)
    (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').obj W')
    (hw' : ∀ ξ : Module.Dual k V, w' ξ = (hk.appLE W W' hWk).hom (w ξ))
    (hw : IsFibreReading V ι f fk i U W hW δ w) :
    IsFibreReading V ι f' fk' i' U' W' hW' ((h.appLE U U' hU').hom δ) w' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq.solution

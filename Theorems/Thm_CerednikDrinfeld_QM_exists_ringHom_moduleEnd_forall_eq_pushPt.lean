import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct

theorem CerednikDrinfeld.QM.exists_ringHom_moduleEnd_forall_eq_pushPt
    {κ : Type} [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ fX)
    (W : Type) [AddCommGroup W] [Module κ W]
    (τW : W → SchemeHomOver (tangentBase κ (RingHom.id κ)) fX)
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX, P ∈ Set.range τW ↔ IsTangentVector L κ (RingHom.id κ) P)
    (hWadd : ∀ v w : W, τW (v + w) = L.mul (tangentBase κ (RingHom.id κ)) (τW v) (τW w))
    (hWsmul : ∀ (a : κ) (v : W), (τW (a • v)).1 = tangentScale κ a ≫ (τW v).1)
    {Λ : Type} [Ring Λ] (ψ : Λ → (X ⟶ X)) (hψ : ∀ x : Λ, ψ x ≫ fX = fX)
    (hψhom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P Q : SchemeHomOver t fX),
      pushPt (ψ x) (hψ x) (L.mul t P Q) = L.mul t (pushPt (ψ x) (hψ x) P) (pushPt (ψ x) (hψ x) Q))
    (hψone : ψ 1 = 𝟙 X) (hψmul : ∀ x y : Λ, ψ (x * y) = ψ y ≫ ψ x)
    (hψadd : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P : SchemeHomOver t fX),
      P.1 ≫ ψ (x + y) = (L.mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψ, P.2]⟩ ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψ, P.2]⟩).1) :
    ∃ θΛ : Λ →+* Module.End κ W, ∀ (x : Λ) (w : W), τW (θΛ x w) = pushPt (ψ x) (hψ x) (τW w) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt.solution

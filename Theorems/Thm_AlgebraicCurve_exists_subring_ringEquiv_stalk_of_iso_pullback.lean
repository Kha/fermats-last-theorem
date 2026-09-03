import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_subring_ringEquiv_stalk_of_iso_pullback

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.exists_subring_ringEquiv_stalk_of_iso_pullback
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)
    (x : X) :
    let 𝒩 : Subring F := SemistableModel.localRing X φ x
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))
    ∃ (𝒩₀ : Subring F) (θ : X₀.presheaf.stalk (pr.base x) ≃+* ↥𝒩₀),
      (∀ g : X₀.presheaf.stalk (pr.base x),
        ((θ g : ↥𝒩₀) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField ((pr.stalkMap x).hom g))) ∧
      (∀ f : F, f ∈ 𝒩₀ ↔ ∃ g : X₀.presheaf.stalk (pr.base x),
        φ f = algebraMap (X.presheaf.stalk x) X.functionField ((pr.stalkMap x).hom g)) ∧
      𝒩₀ ≤ 𝒩 ∧ IsLocalRing ↥𝒩₀ ∧ IsNoetherianRing ↥𝒩₀ ∧
      (∀ a : A₀, algebraMap L F ((ι₀ a : ↥A) : L) ∈ 𝒩₀) ∧
      (∀ a : A₀, ((θ ((X₀.presheaf.germ ⊤ (pr.base x) trivial).hom
          (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a))) : ↥𝒩₀) : F) =
        algebraMap L F ((ι₀ a : ↥A) : L)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_subring_ringEquiv_stalk_of_iso_pullback.solution

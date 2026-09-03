import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.Descent.exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (A₁ : Type u) [CommRing A₁] (j : D.A₀ →+* A₁) (ι₁ : A₁ →+* A) [IsLocalHom ι₁]
    (hι₁ : Function.Injective ι₁) (hcomp : ι₁.comp j = D.ι)
    (K₁ : Subfield L) (range_ι₁ : Set.range (fun a : A₁ => ((ι₁ a : A) : L)) = (A : Set L) ∩ (K₁ : Set L)) :
    ∃ (X₁ : Scheme.{u}) (_ : IsIntegral X₁) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁)) (_ : IsProper f₁) (_ : Flat f₁)
      (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁))),
      e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase ∧
      (∀ x : X₁, IsIntegrallyClosed (X₁.presheaf.stalk x)) ∧
    ∃ (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField),
      (D.F₀ ≤ F₁) ∧ (∀ x : L, x ∈ K₁ → algebraMap L F x ∈ F₁) ∧ Algebra.IsAlgebraic F₁ F ∧
      (∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
          genericPoint X₁,
        ∀ s : F₁, M.ffEquiv (s : F) =
          ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
            ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_Descent_exists_isIntegral_pullback_isIntegrallyClosed_stalk_and_subfield_equiv_functionField_of_range_eq_inter.solution

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.exists_eq_one_add_baseToFunctionField_mul_of_level
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (A₁ : Type u) [CommRing A₁] [IsLocalRing A₁] (ι₁ : A₁ →+* A) [IsLocalHom ι₁]
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (ϖ₁ : A₁) (hϖ₁0 : ϖ₁ ≠ 0) (hϖ₁ : IsLocalRing.maximalIdeal A₁ = Ideal.span {ϖ₁})
    [Flat (Spec.map (CommRingCat.ofHom ι₁))]
    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s)))
    (x : M.X) (u : F) (hu : u ∈ F₁) :
    (∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
        u = 1 + algebraMap L F ((t : A) : L) * r) →
      ∃ t₁ ∈ IsLocalRing.maximalIdeal A₁,
        ∃ s ∈ (algebraMap (X₁.presheaf.stalk
          ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)) X₁.functionField).range,
        φ₁ ⟨u, hu⟩ = 1 + AlgebraicCurve.SemistableModel.baseToFunctionField f₁ t₁ * s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_exists_eq_one_add_baseToFunctionField_mul_of_level.solution

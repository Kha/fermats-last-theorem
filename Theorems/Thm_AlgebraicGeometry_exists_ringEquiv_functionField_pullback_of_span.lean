import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_ringEquiv_functionField_pullback_of_span
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X₀]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hgen : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) = genericPoint X₀)
    {F : Type} [Field F] [Algebra L F]
    (j₀ : X₀.functionField →+* F)
    (hj₀ : ∀ a : A₀, j₀ (SemistableModel.baseToFunctionField toBase₀ a) = algebraMap L F ((ι a : ↥A) : L))
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → X₀.functionField) (d : Fin n → L)
      (g' : Fin n → X₀.functionField),
      (∑ i, d i • j₀ (g' i)) ≠ 0 ∧ f * (∑ i, d i • j₀ (g' i)) = ∑ i, c i • j₀ (g i)) :
    ∃ φ : F ≃+* X.functionField,
      (∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a) ∧
      (∀ g : X₀.functionField,
        φ (j₀ g) =
          ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint X)).hom
            ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_pullback_of_span.solution

import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.toSubring_eq_localRing_of_forall_mem_iff_of_pullback
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] (ι : A₀ →+* ↥A)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsIntegral X₀]
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [IsIntegral X] [IsProper toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    (hgen : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint X) = genericPoint X₀)
    (j₀ : X₀.functionField →+* F)
    (hj₀ : ∀ g : X₀.functionField, φ (j₀ g) =
      ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint X)).hom
        ((X₀.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom g))
    (halgF : ∀ f : F, IsAlgebraic ↥(j₀.range) f)
    (η : X) (hη : toBase.base η = closedPoint ↥A)
    (hfib : ∀ x : X, toBase.base x = closedPoint ↥A →
      (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base x =
        (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η → x = η)
    (hV : ∃ V : ValuationSubring F, V.toSubring = SemistableModel.localRing X φ η)
    (O : ValuationSubring F) (hOA : ∀ a : ↥A, algebraMap L F (a : L) ∈ O)
    (hOtr : ∀ g : X₀.functionField, j₀ g ∈ O ↔
      g ∈ (algebraMap (X₀.presheaf.stalk
              ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base η))
            X₀.functionField).range) :
    O.toSubring = SemistableModel.localRing X φ η := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_toSubring_eq_localRing_of_forall_mem_iff_of_pullback.solution

import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing
    {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))

    (hO : Function.Bijective (fun a : A₀ => toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))

    (hgen₀ : ∀ y : X₀, (toBase₀.base y).asIdeal = ⊥ → y ∈ toBase₀.smoothLocus)

    (hsm₀ : ∀ η₀ : X₀, toBase₀.base η₀ = closedPoint A₀ → (∃ y : X₀, η₀ ⤳ y ∧ y ≠ η₀) → η₀ ∈ toBase₀.smoothLocus)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = toBase)
    [hX : IsIntegral X] :
    let pr := iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))
    pr.base (genericPoint X) = genericPoint X₀ ∧
      (∀ x : X, toBase.base x = closedPoint ↥A ↔ toBase₀.base (pr.base x) = closedPoint A₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → pr.base x = pr.base y → x = y) ∧
      (∀ x₀ : X₀, toBase₀.base x₀ = closedPoint A₀ → ∃ x : X, pr.base x = x₀) ∧
      (∀ x y : X, toBase.base x = closedPoint ↥A → toBase.base y = closedPoint ↥A → (x ⤳ y ↔ pr.base x ⤳ pr.base y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_base_genericPoint_eq_and_bijOn_specialFibre_of_iso_pullback_of_residue_surjective_of_isDiscreteValuationRing.solution

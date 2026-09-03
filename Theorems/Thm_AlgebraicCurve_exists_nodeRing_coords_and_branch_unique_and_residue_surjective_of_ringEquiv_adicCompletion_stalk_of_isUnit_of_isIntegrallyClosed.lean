import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (hres₀ : Function.Surjective ((IsLocalRing.residue ↥A).comp ι₀))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (η₁ η₂ : X) (h₁ : η₁ ⤳ x) (h₂ : η₂ ⤳ x) (h₁x : η₁ ≠ x) (h₂x : η₂ ≠ x) (h₁₂ : η₁ ≠ η₂)
    (hη : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = η₁ ∨ η = η₂)
    {Fbar₁ : Type} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hR₁ : R₁.integers.toSubring = SemistableModel.localRing X φ η₁)
    (hR₂ : R₂.integers.toSubring = SemistableModel.localRing X φ η₂)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w) (hwu : IsUnit ((w : ℕ) : A₀))
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a)) :
    let 𝒩 : Subring F := SemistableModel.localRing X φ x
    ∃ (x₁ : Place (ResidueField ↥A) Fbar₁) (x₂ : Place (ResidueField ↥A) Fbar₂) (S : Set (Place L F)) (xn yn u : F),

      (∀ P : Place L F, P ∈ S ↔
        ∀ f : F, f ∈ 𝒩 → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ 𝒩, f * g = 1)) ∧

      (∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring) ∧
      (∀ a : ↥A, algebraMap L F (a : L) ∈ 𝒩) ∧

      xn ∈ 𝒩 ∧ yn ∈ 𝒩 ∧ u ∈ 𝒩 ∧ (∃ u' ∈ 𝒩, u * u' = 1) ∧
      (∀ h₁ : xn ∈ R₁.integers, R₁.residue ⟨xn, h₁⟩ = 0) ∧
      (∀ h₂ : xn ∈ R₂.integers, x₂.ord (R₂.residue ⟨xn, h₂⟩) = 1) ∧
      (∀ h₂ : yn ∈ R₂.integers, R₂.residue ⟨yn, h₂⟩ = 0) ∧
      (∀ h₁ : yn ∈ R₁.integers, x₁.ord (R₁.residue ⟨yn, h₁⟩) = 1) ∧
      xn * yn = algebraMap L F ((ι₀ ϖ₀ : ↥A) : L) ^ w * u ∧

      (∀ Q' : Place (ResidueField ↥A) Fbar₁,
        (∀ (f : F) (hf : f ∈ R₁.integers), f ∈ 𝒩 → R₁.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) → Q' = x₁) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar₂,
        (∀ (f : F) (hf : f ∈ R₂.integers), f ∈ 𝒩 → R₂.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) → Q' = x₂) ∧

      (∀ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers), f ∈ 𝒩 →
        ∃ (m₁ : R₁.residue ⟨f, hf₁⟩ ∈ x₁.toValuationSubring) (m₂ : R₂.residue ⟨f, hf₂⟩ ∈ x₂.toValuationSubring)
          (c : ResidueField ↥A),
          IsLocalRing.residue ↥x₁.toValuationSubring ⟨_, m₁⟩ = algebraMap (ResidueField ↥A) x₁.ResidueField c ∧
          IsLocalRing.residue ↥x₂.toValuationSubring ⟨_, m₂⟩ = algebraMap (ResidueField ↥A) x₂.ResidueField c) ∧

      (∀ (g₁ : Fbar₁) (g₂ : Fbar₂) (m₁ : g₁ ∈ x₁.toValuationSubring) (m₂ : g₂ ∈ x₂.toValuationSubring) (c : ResidueField ↥A),
        IsLocalRing.residue ↥x₁.toValuationSubring ⟨g₁, m₁⟩ = algebraMap (ResidueField ↥A) x₁.ResidueField c →
        IsLocalRing.residue ↥x₂.toValuationSubring ⟨g₂, m₂⟩ = algebraMap (ResidueField ↥A) x₂.ResidueField c →
          ∃ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers), f ∈ 𝒩 ∧
            R₁.residue ⟨f, hf₁⟩ = g₁ ∧ R₂.residue ⟨f, hf₂⟩ = g₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed.solution

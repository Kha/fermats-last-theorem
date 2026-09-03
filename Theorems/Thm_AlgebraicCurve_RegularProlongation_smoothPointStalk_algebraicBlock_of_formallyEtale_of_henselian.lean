import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    [CharZero L] [IsAlgClosed L] [IsCurveOver L F]
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)

    (K₁ : IntermediateField k₀ L) (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))

    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A)
    (hAS : ∀ a : ↥A₁, algebraMap L F ((a : ↥K₁) : L) ∈ S₁)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)

    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁]
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)

    [IsLocalRing ↥S₁] (hmax : RingHom.ker χ₁ = maximalIdeal ↥S₁)

    (hφs : φ₁.FormallySmooth) (hφu : φ₁.FormallyUnramified) (hφf : φ₁.EssFiniteType)

    (hSR : ∀ f : ↥S₁, (f : F) ∈ R.integers)
    (hcen : ∀ f : ↥S₁, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φ₁ (Polynomial.C ϖ) ∣ f) :
    letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra

    ∀ (F₀ : IntermediateField k₀ F)
      (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
      (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
      (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)),

    (∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c)) ∧

    (∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0) ∧
    maximalIdeal ↥S₁ = Ideal.span {φ₁ (Polynomial.C ϖ), φ₁ Polynomial.X} ∧

    IsNoetherianRing ↥S₁ ∧ UniqueFactorizationMonoid ↥S₁ ∧

    Prime (φ₁ (Polynomial.C ϖ)) ∧
    (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
      (f ∈ R.integers ↔ ∃ g h : ↥S₁, ¬ (φ₁ (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F))) ∧

    (∀ c : ↥A₁, IsLocalRing.residue ↥A ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩ = 0 →
      ∃! χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) ∧
        χ (φ₁ Polynomial.X) = c) ∧
    (∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))}) ∧

    (∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x) ∧

    (∃ G : Finset F, ↑G ⊆ (S₁ : Set F) ∧ ∀ f ∈ S₁, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      (∃ u : (↥S₁)ˣ, ((u : ↥S₁) : F) = h) ∧ f * h = g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_smoothPointStalk_algebraicBlock_of_formallyEtale_of_henselian.solution

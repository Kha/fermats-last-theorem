import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalk_baseChange_layer
attribute [-instance] AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_smoothPointStalk_baseChange_layer
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra L F]
    [CharZero L] [IsAlgClosed L] [IsCurveOver L F]
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)

    (K₁ K₂ : IntermediateField k₀ L) (hK : K₁ ≤ K₂) (halg : ∀ x : L, IsAlgebraic ↥K₁ x)
    (hKfin₂ : FiniteDimensional k₀ ↥K₂)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : L) ∈ A)
    (A₂ : ValuationSubring ↥K₂) (hA₂ : ∀ x : ↥K₂, x ∈ A₂ ↔ (x : L) ∈ A)
    (hκ₁ : Function.Surjective (fun a : ↥A₁ => IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩))
    (hκ₂ : Function.Surjective (fun a : ↥A₂ => IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩))
    (hdvr₁ : IsDiscreteValuationRing ↥A₁) (hdvr₂ : IsDiscreteValuationRing ↥A₂)
    (hhens₁ : HenselianLocalRing ↥A₁) (hhens₂ : HenselianLocalRing ↥A₂)
    (ϖ₂ : ↥A₂) (hϖ₂ : maximalIdeal ↥A₂ = Ideal.span {ϖ₂}) (hϖ₂0 : ϖ₂ ≠ 0)

    (S₁ : Subring F) (φ₁ : Polynomial ↥A₁ →+* ↥S₁) (χ₁ : ↥S₁ →+* ResidueField ↥A) (D₁ : Set (Place L F))
    (hAS : ∀ a : ↥A₁, algebraMap L F ((a : ↥K₁) : L) ∈ S₁)
    (hφs : φ₁.FormallySmooth) (hφu : φ₁.FormallyUnramified)
    (hφC : ∀ a : ↥A₁, ((φ₁ (Polynomial.C a) : ↥S₁) : F) = algebraMap L F ((a : ↥K₁) : L))
    (hχC : ∀ a : ↥A₁, χ₁ (φ₁ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₁) : L), (hA₁ a).mp a.2⟩)
    (hχt : χ₁ (φ₁ Polynomial.X) = 0)
    (hchart : ∀ c : ↥A₁, IsLocalRing.residue ↥A ⟨((c : ↥K₁) : L), (hA₁ c).mp c.2⟩ = 0 →
      ∃! χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) ∧ χ (φ₁ Polynomial.X) = c)
    (hker : ∀ χ : ↥S₁ →+* ↥A₁, (∀ a : ↥A₁, χ (φ₁ (Polynomial.C a)) = a) →
      (∀ f : ↥S₁, IsLocalRing.residue ↥A ⟨((χ f : ↥K₁) : L), (hA₁ _).mp (χ f).2⟩ = χ₁ f) →
      RingHom.ker χ = Ideal.span {φ₁ Polynomial.X - φ₁ (Polynomial.C (χ (φ₁ Polynomial.X)))})
    (hres : ∀ f : ↥S₁, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₁ f))
    (hordQ : ∃ hR : ((φ₁ Polynomial.X : ↥S₁) : F) ∈ R.integers,
      Q.ord (R.residue ⟨((φ₁ Polynomial.X : ↥S₁) : F), hR⟩) = 1)
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))
    (ht : ∀ c : ↥A₁, φ₁ Polynomial.X ≠ φ₁ (Polynomial.C c))
    (hlocal : IsLocalRing ↥S₁) (hmax : ∀ f : ↥S₁, f ∈ maximalIdeal ↥S₁ ↔ χ₁ f = 0)
    (hnoeth : IsNoetherianRing ↥S₁) (hufd : UniqueFactorizationMonoid ↥S₁)
    (ϖ : ↥A₁) (hϖ : maximalIdeal ↥A₁ = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    (hprime : Prime (φ₁ (Polynomial.C ϖ)))
    (hbranch : ∀ p : ↥S₁, Prime p → ¬ Associated p (φ₁ (Polynomial.C ϖ)) →
      ∀ x : ↥S₁, ∃ r : Polynomial ↥A₁, r.Monic ∧ p ∣ (r.map (φ₁.comp Polynomial.C)).eval x)
    (hfg : ∃ G : Finset F, ↑G ⊆ (S₁ : Set F) ∧ ∀ f ∈ S₁, ∃ g h : F,
      g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₁ => algebraMap L F ((a : ↥K₁) : L)) '' Set.univ)) ∧
      (∃ u : (↥S₁)ˣ, ((u : ↥S₁) : F) = h) ∧ f * h = g) :
    letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra
    ∀ (F₀ : IntermediateField k₀ F)
      (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
      (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
      (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
      (hld : ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀) →
        LinearIndependent ↥K₁ c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0)
      (hRint : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ →
        (f ∈ R.integers ↔ ∃ g h : ↥S₁, ¬ (φ₁ (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F))),
    ∃ (S₂ : Subring F) (φ₂ : Polynomial ↥A₂ →+* ↥S₂) (χ₂ : ↥S₂ →+* ResidueField ↥A),

      (∃ hmono : S₁ ≤ S₂,
        S₂ ≤ Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        ((φ₁ Polynomial.X : ↥S₁) : F) = ((φ₂ Polynomial.X : ↥S₂) : F) ∧
        (∀ f : ↥S₁, χ₂ ⟨(f : F), hmono f.2⟩ = χ₁ f)) ∧

      (∀ a : ↥A₂, algebraMap L F ((a : ↥K₂) : L) ∈ S₂) ∧
      φ₂.FormallySmooth ∧ φ₂.FormallyUnramified ∧
      (∀ a : ↥A₂, ((φ₂ (Polynomial.C a) : ↥S₂) : F) = algebraMap L F ((a : ↥K₂) : L)) ∧
      (∀ a : ↥A₂, χ₂ (φ₂ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥K₂) : L), (hA₂ a).mp a.2⟩) ∧
      χ₂ (φ₂ Polynomial.X) = 0 ∧
      (∀ c : ↥A₂, IsLocalRing.residue ↥A ⟨((c : ↥K₂) : L), (hA₂ c).mp c.2⟩ = 0 →
        ∃! χ : ↥S₂ →+* ↥A₂, (∀ a : ↥A₂, χ (φ₂ (Polynomial.C a)) = a) ∧
          (∀ f : ↥S₂, IsLocalRing.residue ↥A ⟨((χ f : ↥K₂) : L), (hA₂ _).mp (χ f).2⟩ = χ₂ f) ∧ χ (φ₂ Polynomial.X) = c) ∧
      (∀ f : ↥S₂, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
          algebraMap (ResidueField ↥A) Q.ResidueField (χ₂ f)) ∧
      (∃ hR : ((φ₂ Polynomial.X : ↥S₂) : F) ∈ R.integers,
        Q.ord (R.residue ⟨((φ₂ Polynomial.X : ↥S₂) : F), hR⟩) = 1) ∧
      (∀ P, P ∈ D₁ ↔ (P.IsRational ∧
        (∀ f : ↥S₂, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥S₂, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₂ f = 0))) ∧
      (∀ c : ↥A₂, φ₂ Polynomial.X ≠ φ₂ (Polynomial.C c)) ∧
      (∃ _ : IsLocalRing ↥S₂, ∀ f : ↥S₂, f ∈ maximalIdeal ↥S₂ ↔ χ₂ f = 0) ∧
      IsNoetherianRing ↥S₂ ∧ UniqueFactorizationMonoid ↥S₂ ∧
      (∀ f : F, f ∈ S₂ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀) ∧
      (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ → ∃ g h : ↥S₂, (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      Prime (φ₂ (Polynomial.C ϖ₂)) ∧
      (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₂ : Set L)) ⊔ F₀ →
        (f ∈ R.integers ↔ ∃ g h : ↥S₂, ¬ (φ₂ (Polynomial.C ϖ₂) ∣ h) ∧ f * (h : F) = (g : F))) ∧
      (∀ χ : ↥S₂ →+* ↥A₂, (∀ a : ↥A₂, χ (φ₂ (Polynomial.C a)) = a) →
        (∀ f : ↥S₂, IsLocalRing.residue ↥A ⟨((χ f : ↥K₂) : L), (hA₂ _).mp (χ f).2⟩ = χ₂ f) →
        RingHom.ker χ = Ideal.span {φ₂ Polynomial.X - φ₂ (Polynomial.C (χ (φ₂ Polynomial.X)))}) ∧
      (∀ p : ↥S₂, Prime p → ¬ Associated p (φ₂ (Polynomial.C ϖ₂)) →
        ∀ x : ↥S₂, ∃ r : Polynomial ↥A₂, r.Monic ∧ p ∣ (r.map (φ₂.comp Polynomial.C)).eval x) ∧
      (∃ G : Finset F, ↑G ⊆ (S₂ : Set F) ∧ ∀ f ∈ S₂, ∃ g h : F,
        g ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        h ∈ Subring.closure (↑G ∪ ((fun a : ↥A₂ => algebraMap L F ((a : ↥K₂) : L)) '' Set.univ)) ∧
        (∃ u : (↥S₂)ˣ, ((u : ↥S₂) : F) = h) ∧ f * h = g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalk_baseChange_layer.solution

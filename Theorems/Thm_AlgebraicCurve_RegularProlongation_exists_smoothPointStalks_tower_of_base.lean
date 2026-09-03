import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalks_tower_of_base
attribute [-instance] AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_smoothPointStalks_tower_of_base
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
    (hcen : ∀ f : ↥S₁, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φ₁ (Polynomial.C ϖ) ∣ f)
    (Q : Place (ResidueField ↥A) Fbar)
    (hK₁ : FiniteDimensional k₀ ↥K₁)

    (D₁ : Set (Place L F))
    (hD : ∀ P, P ∈ D₁ ↔ (P.IsRational ∧
      (∀ f : ↥S₁, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S₁, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₁ f = 0)))
    (hres : ∀ f : ↥S₁, ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₁ f))
    (hordQ : ∃ hR : ((φ₁ Polynomial.X : ↥S₁) : F) ∈ R.integers,
      Q.ord (R.residue ⟨((φ₁ Polynomial.X : ↥S₁) : F), hR⟩) = 1)

    {ι : Type} (K : ι → IntermediateField k₀ L) (hKle : ∀ n, K₁ ≤ K n) (hKfin : ∀ n, FiniteDimensional k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : L) ∈ A)
    (hκn : ∀ n, Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩))
    (hdvrn : ∀ n, IsDiscreteValuationRing ↥(An n)) (hhensn : ∀ n, HenselianLocalRing ↥(An n)) :
    letI : Algebra k₀ F := ((algebraMap L F).comp (algebraMap k₀ L)).toAlgebra
    ∀ (F₀ : IntermediateField k₀ F)
      (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
      (hS₁F₁ : ∀ f : F, f ∈ S₁ → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀)
      (hfrac : ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K₁ : Set L)) ⊔ F₀ → ∃ g h : ↥S₁, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
      (hLD : ∀ (K' : IntermediateField k₀ L), FiniteDimensional k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑K' : Set L)) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0),
    ∃ (Sn : ι → Subring F) (φn : ∀ n, Polynomial ↥(An n) →+* ↥(Sn n)) (χn : ∀ n, ↥(Sn n) →+* ResidueField ↥A),

      (∃ hmono₁ : ∀ n, S₁ ≤ Sn n,
        (∀ n, Sn n ≤ Subring.closure ((S₁ : Set F) ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ))) ∧
        (∀ n, ((φ₁ Polynomial.X : ↥S₁) : F) = ((φn n Polynomial.X : ↥(Sn n)) : F)) ∧
        (∀ n (f : ↥S₁), χn n ⟨(f : F), hmono₁ n f.2⟩ = χ₁ f)) ∧
            (∀ n : ι,

              Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩) ∧

              (∀ a : ↥(An n), algebraMap L F ((a : ↥(K n)) : L) ∈ Sn n) ∧

              (φn n).FormallySmooth ∧ (φn n).FormallyUnramified ∧

              (∀ a : ↥(An n), ((φn n (Polynomial.C a) : ↥(Sn n)) : F) = algebraMap L F ((a : ↥(K n)) : L)) ∧

              (∀ a : ↥(An n), χn n (φn n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩) ∧

              χn n (φn n Polynomial.X) = 0 ∧

              (∀ c : ↥(An n), IsLocalRing.residue ↥A ⟨((c : ↥(K n)) : L), (hAn n c).mp c.2⟩ = 0 →
                ∃! χ : ↥(Sn n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn n (Polynomial.C a)) = a) ∧
                  (∀ f : ↥(Sn n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : L), (hAn n _).mp (χ f).2⟩ = χn n f) ∧
                  χ (φn n Polynomial.X) = c) ∧

              (∀ f : ↥(Sn n), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χn n f)) ∧

              (∃ hR : ((φn n Polynomial.X : ↥(Sn n)) : F) ∈ R.integers,
                Q.ord (R.residue ⟨((φn n Polynomial.X : ↥(Sn n)) : F), hR⟩) = 1) ∧

              (∀ P, P ∈ D₁ ↔ (P.IsRational ∧
                (∀ f : ↥(Sn n), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
                (∀ f : ↥(Sn n), A.valuation (P.evalAt (f : F)) < 1 ↔ χn n f = 0))) ∧

              (∀ c : ↥(An n), φn n Polynomial.X ≠ φn n (Polynomial.C c)) ∧

              (∃ _ : IsLocalRing ↥(Sn n), ∀ f : ↥(Sn n), f ∈ IsLocalRing.maximalIdeal ↥(Sn n) ↔ χn n f = 0) ∧

              IsNoetherianRing ↥(Sn n) ∧ UniqueFactorizationMonoid ↥(Sn n) ∧

              (∀ f : F, f ∈ Sn n → f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀) ∧
              (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀ → ∃ g h : ↥(Sn n), (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧

              (∀ (m : ℕ) (c : Fin m → L) (a : Fin m → F), (∀ i, a i ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀) →
                LinearIndependent ↥(K n) c → ∑ i, algebraMap L F (c i) * a i = 0 → ∀ i, a i = 0) ∧

              (∃ ϖ : ↥(An n), IsLocalRing.maximalIdeal ↥(An n) = Ideal.span {ϖ} ∧ ϖ ≠ 0 ∧
                Prime (φn n (Polynomial.C ϖ)) ∧
                (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap L F) '' (↑(K n) : Set L)) ⊔ F₀ →
                  (f ∈ R.integers ↔ ∃ g h : ↥(Sn n), ¬ (φn n (Polynomial.C ϖ) ∣ h) ∧ f * (h : F) = (g : F))) ∧
                (∀ p : ↥(Sn n), Prime p → ¬ Associated p (φn n (Polynomial.C ϖ)) →
                  ∀ x : ↥(Sn n), ∃ r : Polynomial ↥(An n), r.Monic ∧ p ∣ (r.map ((φn n).comp Polynomial.C)).eval x)) ∧

              (∀ χ : ↥(Sn n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn n (Polynomial.C a)) = a) →
                (∀ f : ↥(Sn n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : L), (hAn n _).mp (χ f).2⟩ = χn n f) →
                RingHom.ker χ = Ideal.span {φn n Polynomial.X - φn n (Polynomial.C (χ (φn n Polynomial.X)))}) ∧

              (∃ G : Finset F, ↑G ⊆ (Sn n : Set F) ∧ ∀ f ∈ Sn n, ∃ g h : F,
                g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ)) ∧
                h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap L F ((a : ↥(K n)) : L)) '' Set.univ)) ∧
                (∃ u : (↥(Sn n))ˣ, ((u : ↥(Sn n)) : F) = h) ∧ f * h = g)) ∧
      (∃ hmono : ∀ n n', K n ≤ K n' → Sn n ≤ Sn n',
      (∀ n n', K n ≤ K n' →
        Sn n' ≤ Subring.closure ((Sn n : Set F) ∪ ((fun a : ↥(An n') => algebraMap (L) F ((a : ↥(K n')) : L)) '' Set.univ))) ∧
      (∀ n n', ((φn n Polynomial.X : ↥(Sn n)) : F) = ((φn n' Polynomial.X : ↥(Sn n')) : F)) ∧
      (∀ n n' (h : K n ≤ K n') (f : ↥(Sn n)), χn n' ⟨(f : F), hmono n n' h f.2⟩ = χn n f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_smoothPointStalks_tower_of_base.solution

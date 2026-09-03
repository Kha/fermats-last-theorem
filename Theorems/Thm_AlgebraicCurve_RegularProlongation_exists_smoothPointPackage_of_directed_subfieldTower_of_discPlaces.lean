import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_smoothPointPackage_of_directed_subfieldTower_of_discPlaces

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_smoothPointPackage_of_directed_subfieldTower_of_discPlaces
    {k₀ L F : Type} [Field k₀] [Field L] [Field F] [Algebra k₀ L] [Algebra k₀ F] [Algebra L F] [IsScalarTower k₀ L F]
    (F₀ : IntermediateField k₀ F)
    (hgen : IntermediateField.adjoin k₀ (Set.range (algebraMap L F)) ⊔ F₀ = ⊤)
    (A : ValuationSubring L)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)

    {ι : Type} [Nonempty ι] (K : ι → IntermediateField k₀ L)
    (hdir : ∀ n n', ∃ l, K n ≤ K l ∧ K n' ≤ K l)
    (hcovL : ∀ x : L, ∃ n, x ∈ K n)
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : L) ∈ A)

    (Sn : ι → Subring F)
    (φn : ∀ n, Polynomial ↥(An n) →+* ↥(Sn n))
    (χn : ∀ n, ↥(Sn n) →+* ResidueField ↥A)
    (Dn : ι → Set (Place L F))
    (hpkg : ∀ n : ι,

      Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : L), (hAn n a).mp a.2⟩) ∧

      (∀ a : ↥(An n), algebraMap (L) F ((a : ↥(K n)) : L) ∈ Sn n) ∧

      (φn n).FormallySmooth ∧ (φn n).FormallyUnramified ∧

      (∀ a : ↥(An n), ((φn n (Polynomial.C a) : ↥(Sn n)) : F) = algebraMap (L) F ((a : ↥(K n)) : L)) ∧

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

      (∀ P, P ∈ Dn n ↔ (P.IsRational ∧
        (∀ f : ↥(Sn n), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥(Sn n), A.valuation (P.evalAt (f : F)) < 1 ↔ χn n f = 0))) ∧

      (∀ χ : ↥(Sn n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn n (Polynomial.C a)) = a) →
        (∀ f : ↥(Sn n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : L), (hAn n _).mp (χ f).2⟩ = χn n f) →
        ∃! P, P ∈ Dn n ∧ ∀ f : ↥(Sn n), P.evalAt (f : F) = ((χ f : ↥(K n)) : L)) ∧

      (∀ P ∈ Dn n, ∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap (L) F) '' (↑(K n) : Set (L))) ⊔ F₀ →
        (f ∈ P.toValuationSubring ↔ ∃ g h : ↥(Sn n), P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F))) ∧

      (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap (L) F) '' (↑(K n) : Set (L))) ⊔ F₀ → f ≠ 0 → (∀ P ∈ Dn n, P.ord f = 0) →
        ∃ (c : ↥(K n)) (u : (↥(Sn n))ˣ), c ≠ 0 ∧ algebraMap (L) F (c : L) * f = ((u : ↥(Sn n)) : F)) ∧

      (∀ f : F, f ∈ IntermediateField.adjoin k₀ (⇑(algebraMap (L) F) '' (↑(K n) : Set (L))) ⊔ F₀ → f ∈ R.integers → (∀ P ∈ Dn n, f ∈ P.toValuationSubring) → f ∈ Sn n) ∧

      (∃ G : Finset F, ↑G ⊆ (Sn n : Set F) ∧ ∀ f ∈ Sn n, ∃ g h : F,
        g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (L) F ((a : ↥(K n)) : L)) '' Set.univ)) ∧
        h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (L) F ((a : ↥(K n)) : L)) '' Set.univ)) ∧
        (∃ u : (↥(Sn n))ˣ, ((u : ↥(Sn n)) : F) = h) ∧ f * h = g))
    (hcompat :
    (∃ hmono : ∀ n n', K n ≤ K n' → Sn n ≤ Sn n',
      (∀ n n', K n ≤ K n' →
        Sn n' ≤ Subring.closure ((Sn n : Set F) ∪ ((fun a : ↥(An n') => algebraMap (L) F ((a : ↥(K n')) : L)) '' Set.univ))) ∧
      (∀ n n', ((φn n Polynomial.X : ↥(Sn n)) : F) = ((φn n' Polynomial.X : ↥(Sn n')) : F)) ∧
      (∀ n n' (h : K n ≤ K n') (f : ↥(Sn n)), χn n' ⟨(f : F), hmono n n' h f.2⟩ = χn n f))) :
    ∃ (S : Subring F) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A) (D : Set (Place L F)),
      (∀ n, Sn n ≤ S) ∧ (∀ f : F, f ∈ S ↔ ∃ n, f ∈ Sn n) ∧
      (∀ n, ((φ Polynomial.X : ↥S) : F) = ((φn n Polynomial.X : ↥(Sn n)) : F)) ∧

      (∀ a : ↥A, algebraMap (L) F (a : (L)) ∈ S) ∧
      (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
      (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : F) = algebraMap (L) F (a : (L))) ∧
      (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
      χ₀ (φ Polynomial.X) = 0 ∧
      (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
        ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
          (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
      (∀ f : ↥(S), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
          algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
      (∃ hR : ((φ Polynomial.X : ↥(S)) : F) ∈ R.integers,
        Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : F), hR⟩) = 1) ∧
      (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥(S), A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
      (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
        (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
        ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : F) = ((χ f : ↥A) : (L))) ∧
      (∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔
        ∃ g h : ↥(S), P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
        ∃ (c : (L)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (L) F c * f = ((u : ↥(S)) : F)) ∧
      (∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_smoothPointPackage_of_directed_subfieldTower_of_discPlaces.solution

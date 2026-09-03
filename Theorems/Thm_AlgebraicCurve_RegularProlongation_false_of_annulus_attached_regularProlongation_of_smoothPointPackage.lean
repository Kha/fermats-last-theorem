import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_false_of_annulus_attached_regularProlongation_of_smoothPointPackage

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.false_of_annulus_attached_regularProlongation_of_smoothPointPackage
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)

    (S : Subring F) (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
    (φ : Polynomial ↥A →+* ↥S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified)
    (hφC : ∀ a : ↥A, ((φ (Polynomial.C a) : ↥S) : F) = algebraMap L F (a : L))
    (χ₀ : ↥S →+* ResidueField ↥A) (hχ₀C : ∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a)
    (hχ₀t : χ₀ (φ Polynomial.X) = 0)

    (hchart : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
      ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c)

    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)
    (hres : ∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f))
    (hordQ : Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : F), hSR (φ Polynomial.X)⟩) = 1)

    (D : Set (Place L F))
    (hD : ∀ P ∈ D, P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))

    (hsec : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
      (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L))

    (hval : ∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F))

    (hloc : ∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
      ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F))
    (hloc' : ∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S)

    (An' An : Annulus A F)
    (hAn : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ (An.modulus : L) ≠ 0 ∧
      An'.param * An.param = algebraMap L F (An.modulus : L))
    (hnear : ∃ hz : An'.param ∈ R.integers, Q.ord (R.residue ⟨An'.param, hz⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord g = 0) →
        ∀ P ∈ An'.dom, ∃ h : P.evalAt g * (P.evalAt An'.param) ^ (-(Q.ord (R.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    {Fbar' : Type*} [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
    (Rx : RegularProlongation A F Fbar') (bx : Place (ResidueField ↥A) Fbar')
    (hfar : ∃ hz : An.param ∈ Rx.integers, bx.ord (Rx.residue ⟨An.param, hz⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ Rx.integers), Rx.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) →
        ∀ P ∈ An.dom, ∃ h : P.evalAt g * (P.evalAt An.param) ^ (-(bx.ord (Rx.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (hdom : ∃ P₁ ∈ An'.dom, ∃ P₂ ∈ An'.dom, A.valuation (P₁.evalAt An'.param) ≠ A.valuation (P₂.evalAt An'.param))

    (hsep : ∃ f : ↥S, χ₀ f = 0 ∧ (f : F) ≠ 0 ∧ (f : F) ∈ Rx.integers ∧ (f : F)⁻¹ ∈ Rx.integers ∧
      ∀ P ∈ An'.dom, P.ord (f : F) = 0) :
    False := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_false_of_annulus_attached_regularProlongation_of_smoothPointPackage.solution

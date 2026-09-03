import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation
    {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    (S : Subring F) (hS : IsLocalRing ↥S)
    (ι : ↥A →+* ↥S) (hι : ∀ a : ↥A, ((ι a : ↥S) : F) = algebraMap L F (a : L))
    (χ₀ : ↥S →+* ResidueField ↥A)
    (hχ₀C : ∀ a : ↥A, χ₀ (ι a) = IsLocalRing.residue ↥A a)
    (hmax : ∀ f : ↥S, f ∈ maximalIdeal ↥S ↔ χ₀ f = 0)
    (t : ↥S)
    (hfrac : ∀ f : F, ∃ g h : ↥S, (h : F) ≠ 0 ∧ f * (h : F) = (g : F))
    (B : ValuationSubring F) (hBA : ∀ c : L, algebraMap L F c ∈ B ↔ c ∈ A) (hSB : ∀ f : ↥S, (f : F) ∈ B)
    (hunitB : ∀ f : ↥S, f ∉ (maximalIdeal ↥A).map ι → (f : F) ≠ 0 ∧ (f : F)⁻¹ ∈ B)
    (hB : ∀ f : F, f ∈ B → ∃ g h : ↥S, h ∉ (maximalIdeal ↥A).map ι ∧ f * (h : F) = (g : F))
    (hprime : ((maximalIdeal ↥A).map ι).IsPrime) (htq : t ∉ (maximalIdeal ↥A).map ι)
    (he1 : ∀ f : F, f ≠ 0 → ∃ c : L, c ≠ 0 ∧ algebraMap L F c * f ∈ B ∧ (algebraMap L F c * f)⁻¹ ∈ B)
    (hhensel : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
      ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) ∧ (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ t = c)
    (hker : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) → (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      RingHom.ker χ = Ideal.span {t - ι (χ t)})
    (hprep : ∀ h : ↥S, h ∉ (maximalIdeal ↥A).map ι →
      ∃ (n : ℕ) (u : (↥S)ˣ) (r : Fin n → ↥A), (∀ i, r i ∈ maximalIdeal ↥A) ∧
        h = (u : ↥S) * ∏ i, (t - ι (r i))) :
    ∃ D : Set (Place L F),
      (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
        (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
      (∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (ι a) = a) → (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
        ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
      (∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔
        ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
      (∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
        ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F)) ∧
      (∀ f : F, f ∈ B → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_disc_sections_locality_of_henselSections_of_weierstrassPreparation.solution

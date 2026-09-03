import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ValuationSubring_ResidueValuationSubring
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one

open Polynomial AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (A₁ A₂ : ValuationSubring L) (h₁ : A ≤ A₁) (h₁₂ : A₁ ≤ A₂)
    [Ring.KrullDimLE 1 (A₁.residueValuationSubring A₂ h₁₂)]
    (hΘ : ∀ (m : L) (x x' y : F) (t t' s : L[X]) (d : ℕ),
      A₂.valuation m < 1 →
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) →
      (A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1) →
      (A.valuation (s.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (s.coeff j) < 1) →
      ((∀ i, x * aeval f t ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → x * aeval f t ∈ V) →
      ((∀ i, x' * aeval f⁻¹ t' ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          x' * aeval f⁻¹ t' ∈ V) →
      ((∀ i, y * aeval f s ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → y * aeval f s ∈ V) →
      x - x' = algebraMap L F m * y →
      ∃ (a : A) (m₁ m₂ : L) (p p' : F) (r r' : L[X]),
        A₂.valuation m₁ < 1 ∧ A₂.valuation m₂ < 1 ∧
        (A.valuation (r.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r.coeff j) < 1) ∧
        (A.valuation (r'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r'.coeff j) < 1) ∧
        ((∀ i, p * aeval f r ∈ (R i).integers) ∧
          ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → p * aeval f r ∈ V) ∧
        ((∀ i, p' * aeval f⁻¹ r' ∈ (R i).integers) ∧
          ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
            p' * aeval f⁻¹ r' ∈ V) ∧
        x = algebraMap L F a + algebraMap L F m₁ * p ∧
        x' = algebraMap L F a + algebraMap L F m₂ * p')
    (m : L) (x x' y : F) (t t' s : L[X]) (d : ℕ)
    (hm : A₁.valuation m < 1)
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (hs : A.valuation (s.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (s.coeff j) < 1)
    (hx : (∀ i, x * aeval f t ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → x * aeval f t ∈ V)
    (hx' : (∀ i, x' * aeval f⁻¹ t' ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        x' * aeval f⁻¹ t' ∈ V)
    (hy : (∀ i, y * aeval f s ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → y * aeval f s ∈ V)
    (hxy : x - x' = algebraMap L F m * y) :
    ∃ (a : A) (m₁ m₂ : L) (p p' : F) (r r' : L[X]),
      A₁.valuation m₁ < 1 ∧ A₁.valuation m₂ < 1 ∧
      (A.valuation (r.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r.coeff j) < 1) ∧
      (A.valuation (r'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (r'.coeff j) < 1) ∧
      ((∀ i, p * aeval f r ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → p * aeval f r ∈ V) ∧
      ((∀ i, p' * aeval f⁻¹ r' ∈ (R i).integers) ∧
        ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          p' * aeval f⁻¹ r' ∈ V) ∧
      x = algebraMap L F a + algebraMap L F m₁ * p ∧
      x' = algebraMap L F a + algebraMap L F m₂ * p'
 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_eq_algebraMap_add_mul_of_valuation_lt_one_of_krullDimLE_one.solution

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq
attribute [-simp] ValuationSubring.coe_toResidueValuationSubring

open Polynomial AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_residue_eq_algebraMap_of_le_of_forall_residue_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A A₁ : ValuationSubring L) (h₁ : A ≤ A₁)
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
    (Fb₁ : ι → Type*) [∀ i, Field (Fb₁ i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A₁) (Fb₁ i)]
    (R₁ : ∀ i, RegularProlongation A₁ F (Fb₁ i))
    (hle : ∀ i, (R i).integers ≤ (R₁ i).integers)
    (htr₁ : ∀ i, Transcendental (IsLocalRing.ResidueField A₁) ((R₁ i).residue ⟨f, hle i (hf i)⟩))
    (x x' : F) (u u' : L) (t t' : L[X])
    (hu : A₁.valuation u = 1) (hu' : A₁.valuation u' = 1)
    (ht : A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1)
    (ht' : A.valuation (t'.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t'.coeff j) < 1)
    (hx : (∀ i, u • x * aeval f t ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u • x * aeval f t ∈ V)
    (hx' : (∀ i, u' • x' * aeval f⁻¹ t' ∈ (R i).integers) ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        u' • x' * aeval f⁻¹ t' ∈ V)
    (hxO : ∀ i, x ∈ (R₁ i).integers) (hx'O : ∀ i, x' ∈ (R₁ i).integers)
    (hxx' : ∀ i, (R₁ i).residue ⟨x, hxO i⟩ = (R₁ i).residue ⟨x', hx'O i⟩) (i : ι) :
    ∃ κ : IsLocalRing.ResidueField A₁,
      (R₁ i).residue ⟨x, hxO i⟩ = algebraMap (IsLocalRing.ResidueField A₁) (Fb₁ i) κ
 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_residue_eq_algebraMap_of_le_of_forall_residue_eq.solution

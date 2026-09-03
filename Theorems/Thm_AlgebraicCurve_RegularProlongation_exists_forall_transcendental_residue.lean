import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_forall_transcendental_residue

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_forall_transcendental_residue
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (hnA : ∀ i, ¬ Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (Fb i)) :
    ∃ f : F, ∃ hf : ∀ i, f ∈ (R i).integers,
      Transcendental L f ∧
      FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F ∧
      ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_transcendental_residue.solution

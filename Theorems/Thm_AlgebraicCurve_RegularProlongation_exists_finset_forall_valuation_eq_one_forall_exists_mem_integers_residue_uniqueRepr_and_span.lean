import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span

set_option autoImplicit false

universe u v

theorem AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    {ι : Type*} [Fintype ι] (y : ι → F)
    (hcard : Fintype.card ι = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hyint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y i ∈ V)
    (hyli : ∀ c : ι → Polynomial L,
      ∑ i, Polynomial.aeval f (c i) * y i = 0 → ∀ i, c i = 0) :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∀ (Fb : Type v) [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) →
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
          ∃ hyO : ∀ i, y i ∈ R.integers,
            (∀ q q' : ι → Polynomial (IsLocalRing.ResidueField A),
              ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q i) * R.residue ⟨y i, hyO i⟩
                = ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q' i) * R.residue ⟨y i, hyO i⟩ →
              q = q') ∧
            ∀ b : Fb, ∃ c : ι →
                IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb),
              b = ∑ i, (c i : Fb) * R.residue ⟨y i, hyO i⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span.solution

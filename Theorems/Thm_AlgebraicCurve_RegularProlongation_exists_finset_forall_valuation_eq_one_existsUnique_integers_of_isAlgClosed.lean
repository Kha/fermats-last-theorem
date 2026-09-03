import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed

set_option autoImplicit false
universe u v

theorem AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F) (hf : Transcendental L f)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F] :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∃ (Fb : Type v) (_ : Field Fb) (_ : Algebra (IsLocalRing.ResidueField A) Fb)
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) ∧
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F ∧
          ∀ (Fb' : Type v) [Field Fb'] [Algebra (IsLocalRing.ResidueField A) Fb']
            (R' : AlgebraicCurve.RegularProlongation A F Fb') (hfR' : f ∈ R'.integers),
            Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨f, hfR'⟩) →
              R'.integers = R.integers := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_existsUnique_integers_of_isAlgClosed.solution

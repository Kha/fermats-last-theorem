import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_annulus_separation_of_crossUnits

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.annulus_separation_of_crossUnits
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (C : ComponentChart A ↥(fieldBar q M') FSS)
    (hCR : C.integers = R.integers)

    (hRC : ∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ C.integers)
    (N : Finset (Place (ResidueField A) FSS))
    (An : ↥N → Annulus A ↥(fieldBar q M'))

    (hatt : ∀ x : ↥N, ((An x).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
      ∃ hz : (An x).param ∈ R.integers, (x : Place (ResidueField A) FSS).ord (R.residue ⟨(An x).param, hz⟩) = 1 ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ (An x).dom, P.ord f = 0) →
          ∀ P ∈ (An x).dom,
            ∃ h : P.evalAt f * (P.evalAt (An x).param) ^ (-((x : Place (ResidueField A) FSS).ord (R.residue ⟨f, hf⟩))) ∈ A,
              IsUnit (⟨_, h⟩ : A))

    (hfin : ∀ f : ↥(fieldBar q M'), f ≠ 0 → Set.Finite {P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') | P.ord f ≠ 0})

    (hcross : ∀ x x' : ↥N, x ≠ x' →
      ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 ∧
        (x : Place (ResidueField A) FSS).ord (R.residue ⟨g, hg⟩) ≠ 0 ∧
        (∀ P ∈ (An x).dom, P.ord g = 0) ∧
        (∀ P ∈ (An x').dom, g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : A))) :

    (∀ (O : ValuationSubring ↥(fieldBar q M')) (x x' : ↥N),
      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A) →
      (∃ t : ↥(fieldBar q M'), t ∈ O ∧ ∀ a : A,
          ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O, IsUnit (⟨_, h⟩ : O)) →
      ¬ (∀ f : ↥(fieldBar q M'), (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
      (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An x).dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) →
      (∀ f : ↥(fieldBar q M'), (∀ P ∈ (An x').dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) → f ∈ O) → x = x') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_annulus_separation_of_crossUnits.solution

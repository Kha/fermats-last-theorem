import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_levelAut_ord_residue_pos_and_not_of_levelOrbits

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.exists_levelAut_ord_residue_pos_and_not_of_levelOrbits
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (hint : ∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers)
    (N : Finset (Place (ResidueField A) FSS))

    (heqvN : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
        ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
      ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
        (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N))

    (hfree : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
        (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
        R.resAut (levelAutBar q M' ζ γ) hτ • Q ≠ Q)

    (C : ComponentChart A ↥(fieldBar q M') FSS)
    (hCR : C.integers = R.integers)
    (hCres : ∀ (f : ↥(fieldBar q M')) (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩)

    (hdict : (∀ 𝔪 : Ideal ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal →
          ∃! Q : Place (ResidueField A) FSS, Q ∉ N ∧
            ∀ g : ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : FSS) = 0 ∨ 0 < Q.ord (g : FSS)) ∧
        ∀ Q : Place (ResidueField A) FSS, Q ∉ N →
          ∃ 𝔪 : Ideal ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), 𝔪.IsMaximal ∧
            ∀ g : ↥(⨅ (Q : Place (ResidueField A) FSS) (_ : Q ∉ N), Q.toValuationSubring.toSubring), g ∈ 𝔪 ↔ (g : FSS) = 0 ∨ 0 < Q.ord (g : FSS))

    (hlift : ∀ g : FSS, (∀ Q : Place (ResidueField A) FSS, Q ∉ N → g ∈ Q.toValuationSubring) →
      ∃ (f : ↥(fieldBar q M')) (hf : f ∈ C.integers),
        (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧ C.residue ⟨f, hf⟩ = g) :

    (∀ Q : Place (ResidueField A) FSS, Q ∉ N →
      ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧
        ∃ (f : ↥(fieldBar q M')) (hf : f ∈ C.integers) (hf' : levelAutBar q M' ζ γ f ∈ C.integers),
          (∀ P ∈ C.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) ∧
          0 < Q.ord (C.residue ⟨f, hf⟩) ∧ ¬ 0 < Q.ord (C.residue ⟨levelAutBar q M' ζ γ f, hf'⟩)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_levelAut_ord_residue_pos_and_not_of_levelOrbits.solution

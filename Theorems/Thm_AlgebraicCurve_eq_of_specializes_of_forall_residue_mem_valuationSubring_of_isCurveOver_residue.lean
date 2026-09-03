import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue
attribute [-simp] AlgebraicCurve.RegularProlongation.coe_integersEquiv AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (η : X) (hη : toBase.base η = closedPoint ↥A) (hηnc : ∃ y : X, η ⤳ y ∧ y ≠ η)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    [AlgebraicCurve.IsCurveOver (IsLocalRing.ResidueField ↥A) Fbar] [Algebra.EssFiniteType (IsLocalRing.ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (Q' : Place (ResidueField ↥A) Fbar) (x₁ x₂ : X)
    (hx₁ : toBase.base x₁ = closedPoint ↥A) (hx₁c : ∀ y : X, x₁ ⤳ y → y = x₁)
    (hx₂ : toBase.base x₂ = closedPoint ↥A) (hx₂c : ∀ y : X, x₂ ⤳ y → y = x₂)
    (h₁ : η ⤳ x₁) (h₂ : η ⤳ x₂)
    (hr₁ : ∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₁ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring)
    (hr₂ : ∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₂ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) :
    x₁ = x₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_eq_of_specializes_of_forall_residue_mem_valuationSubring_of_isCurveOver_residue.solution

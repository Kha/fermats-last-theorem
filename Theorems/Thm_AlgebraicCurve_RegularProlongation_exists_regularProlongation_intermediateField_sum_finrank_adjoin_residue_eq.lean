import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq.{u}
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type u} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    {L₁ : Type*} [Field L₁] [IsAlgClosed L₁] [Algebra L₁ L] [Algebra L₁ F] [IsScalarTower L₁ L F]
    (F₁ : IntermediateField L₁ F) (hf₁ : f ∈ F₁)
    (hfd₁ : FiniteDimensional (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁)
    (hdeg : Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ≤
      Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hsep : ∀ i j, i ≠ j → ∃ u ∈ F₁, ¬ (u ∈ (R i).integers ↔ u ∈ (R j).integers))
    (hbas : ∀ i, ∃ (b : Fin (Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)) → F) (hb : ∀ l, b l ∈ (R i).integers),
        (∀ l, b l ∈ F₁) ∧
        LinearIndependent (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)))
          (fun l => (R i).residue ⟨b l, hb l⟩)) :
    ∃ (Fb₁ : ι → Type u) (_ : ∀ i, Field (Fb₁ i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i))
      (R₁ : ∀ i, RegularProlongation (A.comap (algebraMap L₁ L)) F₁ (Fb₁ i))
      (φ : ∀ i, Fb₁ i →+* Fb i)
      (hO : ∀ i (u : F₁), u ∈ (R₁ i).integers ↔ (u : F) ∈ (R i).integers),
      Function.Injective (fun i => (R₁ i).integers) ∧
      (∀ i (u : F₁) (hu : (u : F) ∈ (R i).integers),
        φ i ((R₁ i).residue ⟨u, (hO i u).mpr hu⟩) = (R i).residue ⟨u, hu⟩) ∧
      (∀ i (a : A.comap (algebraMap L₁ L)),
        φ i (algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L))) (Fb₁ i)
          (IsLocalRing.residue _ a)) =
        algebraMap (IsLocalRing.ResidueField A) (Fb i)
          (IsLocalRing.residue A ⟨algebraMap L₁ L a, ValuationSubring.mem_comap.mp a.2⟩)) ∧
      Transcendental L₁ (⟨f, hf₁⟩ : F₁) ∧
      (∀ i, Transcendental (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
        ((R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩)) ∧
      ∑ i, Module.finrank (IntermediateField.adjoin
          (IsLocalRing.ResidueField (A.comap (algebraMap L₁ L)))
          ({(R₁ i).residue ⟨⟨f, hf₁⟩, (hO i _).mpr (hf i)⟩} : Set (Fb₁ i))) (Fb₁ i)
        = Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ ∧
      Module.finrank (IntermediateField.adjoin L₁ ({(⟨f, hf₁⟩ : F₁)} : Set F₁)) F₁ =
        Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_intermediateField_sum_finrank_adjoin_residue_eq.solution

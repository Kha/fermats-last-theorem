import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Galois.Basic
import P2M.Util
import P2M.Sol.S_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois

theorem ValuationSubring.normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    [IsGalois E F]
    (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O)
    [Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')]
    (hcompat : ∀ a : O, algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O')
        (IsLocalRing.residue O a) = IsLocalRing.residue O' ⟨algebraMap E F a, (hO a).mpr a.2⟩) :
    (∀ (σ : O'.decompositionSubgroup E) (a : IsLocalRing.ResidueField O),
        σ • algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') a =
          algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') a) ∧
    Normal (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') ∧
    ∀ τ : IsLocalRing.ResidueField O' ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O',
      ∃ σ : O'.decompositionSubgroup E, ∀ x : IsLocalRing.ResidueField O', σ • x = τ x := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_normal_residueField_and_forall_algEquiv_exists_smul_eq_of_isGalois.solution

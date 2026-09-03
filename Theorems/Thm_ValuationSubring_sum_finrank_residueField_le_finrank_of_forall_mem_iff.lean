import Mathlib.RingTheory.Valuation.ValuationSubring
import P2M.Util
import P2M.Sol.S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff

theorem ValuationSubring.sum_finrank_residueField_le_finrank_of_forall_mem_iff
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    (O : ValuationSubring E)
    {ι : Type*} [Fintype ι]
    (O' : ι → ValuationSubring F)
    (hinj : Function.Injective O')
    (hO : ∀ (j : ι) (x : E), algebraMap E F x ∈ O' j ↔ x ∈ O)
    [∀ j, Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))]
    (hcompat : ∀ (j : ι) (a : O), algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))
        (IsLocalRing.residue O a) = IsLocalRing.residue (O' j) ⟨algebraMap E F a, (hO j a).mpr a.2⟩) :
    (∀ j, FiniteDimensional (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))) ∧
      ∑ j, Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j)) ≤ Module.finrank E F := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff.solution

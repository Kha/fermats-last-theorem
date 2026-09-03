import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_trdeg_residueField_le_trdeg

set_option autoImplicit false

theorem ValuationSubring.trdeg_residueField_le_trdeg
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_trdeg_residueField_le_trdeg.solution

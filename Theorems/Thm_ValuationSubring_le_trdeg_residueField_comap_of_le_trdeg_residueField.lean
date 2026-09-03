import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_le_trdeg_residueField_comap_of_le_trdeg_residueField

set_option autoImplicit false

universe u

theorem ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L]
    (A : ValuationSubring L) (hk : ∀ x : k, algebraMap k L x ∈ A)
    (nK nL : ℕ) (hK : Algebra.trdeg k K = nK) (hL : Algebra.trdeg k L = nL)
    (hA : letI : Algebra k (IsLocalRing.ResidueField A) :=
        ((IsLocalRing.residue A).comp ((algebraMap k L).codRestrict A.toSubring hk)).toAlgebra
      ((nL - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField A)) :
    letI O : ValuationSubring K := A.comap (algebraMap K L)
    letI hkO : ∀ x : k, algebraMap k K x ∈ O := fun x => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hk x
    letI : Algebra k (IsLocalRing.ResidueField O) :=
      ((IsLocalRing.residue O).comp ((algebraMap k K).codRestrict O.toSubring hkO)).toAlgebra
    ((nK - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_le_trdeg_residueField_comap_of_le_trdeg_residueField.solution

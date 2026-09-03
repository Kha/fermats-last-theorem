import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_of_formallyUnramified_residueField_baseChange
open scoped TensorProduct

theorem Algebra.Etale.of_formallyUnramified_residueField_baseChange (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.Etale R S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_of_formallyUnramified_residueField_baseChange.solution

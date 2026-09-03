import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite
open scoped TensorProduct

theorem Algebra.FormallyUnramified.of_residueField_baseChange_of_finite (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.solution

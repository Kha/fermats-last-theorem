import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two

open IsLocalRing

theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (hdim : ringKrullDim R ≤ 2) :
    UniqueFactorizationMonoid R := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two.solution

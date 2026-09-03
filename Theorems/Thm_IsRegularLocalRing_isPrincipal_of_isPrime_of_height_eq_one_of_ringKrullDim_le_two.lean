import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two

open IsLocalRing

theorem IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (P : Ideal R) (hP : P.IsPrime) (hP1 : P.height = 1) :
    Submodule.IsPrincipal P := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two.solution

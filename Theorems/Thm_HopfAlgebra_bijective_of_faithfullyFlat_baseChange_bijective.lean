import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective

universe u v

theorem HopfAlgebra.bijective_of_faithfullyFlat_baseChange_bijective
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H']
    (φ : H →ₐc[R] H') (hφ : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange R')) :
    Function.Bijective φ := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bijective_of_faithfullyFlat_baseChange_bijective.solution

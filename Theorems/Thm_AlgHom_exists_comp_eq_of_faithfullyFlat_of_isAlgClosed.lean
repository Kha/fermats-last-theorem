import Mathlib
import P2M.Util
import P2M.Sol.S_AlgHom_exists_comp_eq_of_faithfullyFlat_of_isAlgClosed

universe u v w

theorem AlgHom.exists_comp_eq_of_faithfullyFlat_of_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K]
    (R : Type v) [CommRing R] [Algebra K R]
    (S : Type w) [CommRing S] [Algebra K S] [Module.Finite K S]
    [Algebra R S] [IsScalarTower K R S] [Module.FaithfullyFlat R S]
    (x : R →ₐ[K] K) :
    ∃ y : S →ₐ[K] K, y.comp (IsScalarTower.toAlgHom K R S) = x := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_exists_comp_eq_of_faithfullyFlat_of_isAlgClosed.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
    (T : Type u) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (K : Type u) [Field K] [Algebra (ResidueField T) K] [Algebra.IsAlgebraic (ResidueField T) K] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : Algebra T B)
      (_ : IsLocalHom (algebraMap T B)),
      Module.FaithfullyFlat T B ∧
        Ideal.map (algebraMap T B) (maximalIdeal T) = maximalIdeal B ∧
        Nonempty (ResidueField B ≃ₐ[ResidueField T] K) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic.solution

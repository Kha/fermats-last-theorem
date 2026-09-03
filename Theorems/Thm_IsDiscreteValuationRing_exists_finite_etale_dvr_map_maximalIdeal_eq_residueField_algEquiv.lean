import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv

set_option autoImplicit false

universe u v

theorem IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k' : Type v) [Field k'] [Algebra (IsLocalRing.ResidueField R) k'] [FiniteDimensional (IsLocalRing.ResidueField R) k']
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) k'] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      Nonempty (k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R') := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv.solution

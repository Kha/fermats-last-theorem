import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_residueField_algHom

set_option autoImplicit false

universe u w
theorem IsDiscreteValuationRing.exists_finite_etale_isAdicComplete_residueField_algHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (p : ℕ) (hunif : Irreducible (p : R))
    (k₀ : Type w) [Field k₀] [Algebra (IsLocalRing.ResidueField R) k₀]
    [FiniteDimensional (IsLocalRing.ResidueField R) k₀] [Algebra.IsSeparable (IsLocalRing.ResidueField R) k₀] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : CharZero R')
      (_ : Algebra R R') (_ : Module.Finite R R') (_ : Module.Free R R') (_ : Algebra.Etale R R')
      (hloc : IsLocalHom (algebraMap R R')),
      IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧ Irreducible (p : R') ∧
      ∃ e : k₀ →+* IsLocalRing.ResidueField R',
        e.comp (algebraMap (IsLocalRing.ResidueField R) k₀)
          = @IsLocalRing.ResidueField.map R R' _ _ _ _ (algebraMap R R') hloc := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finite_etale_isAdicComplete_residueField_algHom.solution

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.CharZero.Defs
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_finite_extension_residueField_splits_quadratic

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_finite_extension_residueField_splits_quadratic
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)] [CharZero 𝒪] :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪')
      (_ : Finite (IsLocalRing.ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪')),
    Function.Injective (algebraMap 𝒪 𝒪') ∧
    ∀ a b : IsLocalRing.ResidueField 𝒪, ∃ x y : IsLocalRing.ResidueField 𝒪',
      ∀ z : IsLocalRing.ResidueField 𝒪',
        z ^ 2 - IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') a * z + IsLocalRing.ResidueField.map (algebraMap 𝒪 𝒪') b =
          (z - x) * (z - y) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_finite_extension_residueField_splits_quadratic.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (L : Type) [Field L] [Algebra 𝒪 L] (hL : Function.Injective (algebraMap 𝒪 L))
    (χ : A →ₐ[𝒪] L) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪'))
      (j : 𝒪' →ₐ[𝒪] L) (ψ : A →ₐ[𝒪] 𝒪'),
      Function.Injective j ∧ ∀ a : A, j (ψ a) = χ a := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite.solution

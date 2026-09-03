import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing

set_option autoImplicit false

theorem RibetIrr.module_finite_padicInt_of_isDiscreteValuationRing
    (p : ℕ) [Fact p.Prime] (𝒪'' : Type) [CommRing 𝒪''] [IsDomain 𝒪'']
    [IsDiscreteValuationRing 𝒪''] [Finite (IsLocalRing.ResidueField 𝒪'')]
    [CharZero 𝒪''] (hp𝒪'' : (p : 𝒪'') ∈ IsLocalRing.maximalIdeal 𝒪'')
    [Algebra ℤ_[p] 𝒪''] : Module.Finite ℤ_[p] 𝒪'' := by p2m_exact_reverting @_root_.P2MW.S_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (B : ValuationSubring F) (hCB : ∀ c : C, algebraMap C F c ∈ B)
    (hCBmax : ∀ c : C, algebraMap C F c ∈ B.nonunits ↔ c ∈ maximalIdeal C) :
    IsDiscreteValuationRing ↥B := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.solution

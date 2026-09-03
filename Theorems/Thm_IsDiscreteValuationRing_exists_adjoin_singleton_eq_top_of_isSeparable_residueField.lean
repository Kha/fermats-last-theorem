import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField
attribute [-instance] ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal
attribute [-simp] Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_adjoin_singleton_eq_top_of_isSeparable_residueField
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (hinj : Function.Injective (algebraMap A B)) :
    ∃ x : B, Algebra.adjoin A {x} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.solution

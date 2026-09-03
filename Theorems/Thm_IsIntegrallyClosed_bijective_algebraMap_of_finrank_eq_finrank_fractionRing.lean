import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing

set_option autoImplicit false

theorem IsIntegrallyClosed.bijective_algebraMap_of_finrank_eq_finrank_fractionRing
    {O W C : Type*} [CommRing O] [IsDomain O] [CommRing W] [IsDomain W] [IsIntegrallyClosed W]
    [CommRing C] [IsDomain C]
    [Algebra O W] [Module.Finite O W] [Module.Free O W] [FaithfulSMul O W]
    [Algebra O C] [Algebra.IsIntegral O C] [Algebra W C] [IsScalarTower O W C] [FaithfulSMul W C]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    (h : Module.finrank O W = Module.finrank K₁ K) :
    Function.Bijective (algebraMap W C) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing.solution

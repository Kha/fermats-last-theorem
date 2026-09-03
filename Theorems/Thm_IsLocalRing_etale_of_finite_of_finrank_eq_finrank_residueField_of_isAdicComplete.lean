import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete

set_option autoImplicit false

open IsLocalRing in

theorem IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete
    {O C : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O]
    [IsAdicComplete (maximalIdeal O) O]
    [CommRing C] [IsDomain C] [IsLocalRing C] [IsAdicComplete (maximalIdeal C) C]
    [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [IsLocalHom (algebraMap O C)]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [Algebra.IsSeparable (ResidueField O) (ResidueField C)]
    (hcount : Module.finrank K₁ K = Module.finrank (ResidueField O) (ResidueField C)) :
    Algebra.Etale O C := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField_of_isAdicComplete.solution

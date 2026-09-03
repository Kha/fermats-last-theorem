import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.LevelN.exists_linearMap_regularDifferentials_cuspForm_injective
    (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ Φ : AlgebraicCurve.regularDifferentials ℂ K →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma N) 2,
      Function.Injective Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.solution

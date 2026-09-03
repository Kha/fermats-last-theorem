import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_diffQExp_map_eq_coeffMap_diffQExp

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.diffQExp_map_eq_coeffMap_diffQExp
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (Γ : Subgroup SL(2, ℤ))
    [Algebra ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)] [Algebra k ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    [IsScalarTower k K ↥(ModularCurve.qExpFunctionFieldC K Γ)] [IsScalarTower k ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    [SMulCommClass K ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hι : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k Γ),
      ((algebraMap ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) =
        ModularCurve.coeffMap (algebraMap k K) (x : LaurentSeries k))
    (ω : Ω[↥(ModularCurve.qExpFunctionFieldC k Γ)⁄k]) :
    ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ) (KaehlerDifferential.map k K ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) ω) =
      ModularCurve.coeffMap (algebraMap k K) (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC k Γ) ω) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diffQExp_map_eq_coeffMap_diffQExp.solution

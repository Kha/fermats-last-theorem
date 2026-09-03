import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.isModuliPlaceOf_map_frobenius_smul {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (N : ℕ) [NeZero N]
    (σ : SemilinearAut κ ↥(modularFunctionFieldFullC κ N))
    (hσ : ∀ x : ↥(modularFunctionFieldFullC κ N),
      ((σ • x : ↥(modularFunctionFieldFullC κ N)) : LaurentSeries κ) = coeffMap (frobenius κ q') (x : LaurentSeries κ))
    (x : ModuliPoint N κ) (v : Place κ ↥(modularFunctionFieldFullC κ N))
    (hv : IsModuliPlaceOf κ N x v) :
    IsModuliPlaceOf κ N (ModuliPoint.map (frobenius κ q') x) (σ • v) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul.solution

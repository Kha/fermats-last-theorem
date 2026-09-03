import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import P2M.Util
namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_coe_eq_jqModC_fbar

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] :
    ∃ xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
  refine ⟨⟨jqModC (ResidueField ↥A), ?_⟩, rfl⟩
  exact x0_le_xHFunctionFieldC (K := ResidueField ↥A) (M := M / p) (H := infSubgroup p M H hpM)
    (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 (ResidueField ↥A) (M / p)
      (jqModC_mem_full (K := ResidueField ↥A) (N := M / p)))

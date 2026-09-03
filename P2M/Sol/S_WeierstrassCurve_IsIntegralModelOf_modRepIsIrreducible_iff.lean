import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_WeierstrassCurve_galoisRepIsIrreducible_iff_of_variableChange_eq
import P2M.Util
namespace P2MW.S_WeierstrassCurve_IsIntegralModelOf_modRepIsIrreducible_iff

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ} (h : W.IsIntegralModelOf E) (n : ℕ) : W.ModRepIsIrreducible n ↔ Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E n := by
  obtain ⟨C, hC⟩ := h
  exact (WeierstrassCurve.galoisRepIsIrreducible_iff_of_variableChange_eq (AlgebraicClosure ℚ) C hC n).symm

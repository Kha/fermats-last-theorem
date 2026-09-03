import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
namespace P2MW.S_FreyPackage_freyCurve_discriminant

open WeierstrassCurve

theorem solution (P : FreyPackage) :
    P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  have h : ((P.c : ℚ)) ^ P.p = (P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p := by
    exact_mod_cast P.hFLT.symm
  have key : ((P.a : ℚ) * P.b * P.c) ^ (2 * P.p)
      = ((P.a : ℚ) ^ P.p) ^ 2 * ((P.b : ℚ) ^ P.p) ^ 2 * ((P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p) ^ 2 := by
    rw [← h]
    ring
  rw [key]
  simp only [FreyPackage.freyCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

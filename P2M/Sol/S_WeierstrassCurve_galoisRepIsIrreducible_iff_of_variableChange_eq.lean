import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_exists_linearEquiv_torsionBy_of_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_galoisRepIsIrreducible_iff_of_linearEquiv
import P2M.Util
namespace P2MW.S_WeierstrassCurve_galoisRepIsIrreducible_iff_of_variableChange_eq

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K] {E E' : WeierstrassCurve F} (C : VariableChange F) (hC : C • E = E') (n : ℕ) : Affine.Point.GaloisRepIsIrreducible (K := K) F E n ↔ Affine.Point.GaloisRepIsIrreducible (K := K) F E' n := by
  obtain ⟨φ, hφ⟩ := WeierstrassCurve.exists_linearEquiv_torsionBy_of_variableChange_eq K C hC n
  exact WeierstrassCurve.Affine.Point.galoisRepIsIrreducible_iff_of_linearEquiv φ hφ

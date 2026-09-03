import Definitions.Def_FLTPrelim_GaloisRep
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_galoisRepIsIrreducible_iff_of_variableChange_eq

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.galoisRepIsIrreducible_iff_of_variableChange_eq {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K] {E E' : WeierstrassCurve F} (C : VariableChange F) (hC : C • E = E') (n : ℕ) : Affine.Point.GaloisRepIsIrreducible (K := K) F E n ↔ Affine.Point.GaloisRepIsIrreducible (K := K) F E' n := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_galoisRepIsIrreducible_iff_of_variableChange_eq.solution

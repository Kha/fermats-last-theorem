import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.KrullTopology
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_invariants_le_invariants_of_le
import Definitions.Def_Compat_Mathlib430

open ModularCurve AlgebraicCurve
theorem ModularCurve.JZero.invariants_le_invariants_of_le (N : ℕ) [NeZero N]
    (K L' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L') :
    JZero N ^+ ↥K.fixingSubgroup ≤ JZero N ^+ ↥L'.fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_invariants_le_invariants_of_le.solution

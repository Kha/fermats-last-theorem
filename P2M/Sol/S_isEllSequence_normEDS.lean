import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_WeierstrassCurve_EDSEngine
import P2M.Util
import Definitions.Def_Compat_Mathlib430
namespace P2MW.S_isEllSequence_normEDS

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R] (b c d : R) :
    IsEllSequence' (normEDS b c d) :=
  IsEllSequence'.normEDS

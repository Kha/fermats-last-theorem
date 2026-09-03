import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

theorem NumberField.ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one
    (E K L : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L] [IsNormalClosure E K L]
    (v : HeightOneSpectrum (𝓞 E))
    (hK : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) = v → v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_ramificationIdxIn_eq_one_of_isNormalClosure_of_forall_ramificationIdx_eq_one.solution

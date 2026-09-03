import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import P2M.Util
import P2M.Sol.S_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.RigidWeierstrassData.exists_eq_act_of_mk_eq_mk
    {A : Type} [CommRing A] (R : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] (x y : R.Raw T)
    (h : (Quot.mk _ x : R.Pt T) = Quot.mk _ y) :
    ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk.solution

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import P2M.Util
namespace P2MW.S_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk

set_option autoImplicit false

open ModularCurve

theorem solution
    {A : Type} [CommRing A] (R : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] (x y : R.Raw T)
    (h : (Quot.mk _ x : R.Pt T) = Quot.mk _ y) :
    ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x := by
  have hequiv : Equivalence (R.Rel (T := T)) :=
    { refl := fun a => ModularCurve.RigidWeierstrassData.Rel.refl R a
      symm := by
        rintro a b ⟨C, rfl⟩
        refine ⟨C⁻¹, ?_⟩
        rw [← R.act_mul, inv_mul_cancel, R.act_one]
      trans := fun h₁ h₂ => ModularCurve.RigidWeierstrassData.Rel.trans R h₁ h₂ }
  have h' : Relation.EqvGen (R.Rel (T := T)) x y := Quot.eqvGen_exact h
  exact (hequiv.eqvGen_iff).mp h'

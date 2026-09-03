import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P₀ : LevelModuliPackageAbs A D)
    (T : Type u) [CommRing T] [Algebra A T] (t : T) :
    Nat.card {φ : P₀.B₀ →ₐ[A] T // φ (D.jOf P₀.univ) = t} = Nat.card {x : D.Pt T // D.jOf x = t} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq.solution

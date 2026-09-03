import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P₀ : LevelModuliPackageAbs A D)
    (T : Type u) [CommRing T] [Algebra A T] (t : T) :
    Nat.card {φ : P₀.B₀ →ₐ[A] T // φ (D.jOf P₀.univ) = t} = Nat.card {x : D.Pt T // D.jOf x = t} := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun φ => ⟨D.map φ.1 P₀.univ, by rw [D.jOf_map]; exact φ.2⟩
      invFun := fun x => ⟨P₀.classify x.1, by rw [← D.jOf_map, P₀.map_classify]; exact x.2⟩
      left_inv := fun φ => ?_
      right_inv := fun x => ?_ }
  · apply Subtype.ext
    exact (P₀.classify_unique _ φ.1 rfl).symm
  · apply Subtype.ext
    exact P₀.map_classify x.1

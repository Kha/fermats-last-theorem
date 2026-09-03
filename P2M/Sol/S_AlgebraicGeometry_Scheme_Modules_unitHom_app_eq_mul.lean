import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_unitHom_app_eq_mul

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace P2mWs30UnitEnd

variable {X : Scheme.{u}}

theorem smul_unit_eq_mul (U : X.Opens) (r : Γ(X, U)) (x : Γ(𝟙_ X.Modules, U)) :
    (show Γ(X, U) from r • x) = r * (show Γ(X, U) from x) := rfl

theorem unit_map_eq (U V : X.Opens) (i : V ≤ U) (x : Γ(𝟙_ X.Modules, U)) :
    (show Γ(X, V) from (𝟙_ X.Modules).presheaf.map (homOfLE i).op x) =
      X.presheaf.map (homOfLE i).op (show Γ(X, U) from x) := rfl

end P2mWs30UnitEnd

open P2mWs30UnitEnd in
theorem solution
    {X : Scheme.{u}} (c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    (show Γ(X, U) from c.app U m) =
      X.presheaf.map (homOfLE (le_top (a := U))).op (show Γ(X, ⊤) from c.app ⊤ (1 : Γ(X, ⊤))) *
        (show Γ(X, U) from m) := by

  have hnat0 := ConcreteCategory.congr_hom (c.mapPresheaf.naturality (homOfLE (le_top (a := U))).op)
    (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))
  have hnat : c.app U ((𝟙_ X.Modules).presheaf.map (homOfLE (le_top (a := U))).op
      (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))) =
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top (a := U))).op
        (c.app ⊤ (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))) := hnat0
  have h1U : (𝟙_ X.Modules).presheaf.map (homOfLE (le_top (a := U))).op (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤))) =
      (show Γ(𝟙_ X.Modules, U) from (1 : Γ(X, U))) := by
    change X.presheaf.map (homOfLE (le_top (a := U))).op (1 : Γ(X, ⊤)) = (1 : Γ(X, U))
    exact map_one _
  have e1 : ((show Γ(X, U) from m) • (show Γ(𝟙_ X.Modules, U) from (1 : Γ(X, U))) : Γ(𝟙_ X.Modules, U)) = m :=
    mul_one (show Γ(X, U) from m)
  conv_lhs => rw [← e1]
  rw [Scheme.Modules.Hom.app_smul]
  change (show Γ(X, U) from m) * (show Γ(X, U) from c.app U (show Γ(𝟙_ X.Modules, U) from (1 : Γ(X, U)))) = _
  rw [mul_comm]
  congr 1
  rw [← h1U, hnat]
  rfl

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_tensorPow

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard"

namespace AezTensorPow

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard"

private theorem _root_.AezTensorPow.unit {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k)) :
    IsAlgEquivZero a (𝟙_ A.Modules) := by
  refine ⟨Spec (CommRingCat.of k), 𝟙 _, inferInstance, geometricallyIntegral_id_Spec k,
    SheafOfModules.unit (Limits.pullback a (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf,
    Scheme.Modules.isInvertible_unit _, ⟨𝟙 _, Category.comp_id _⟩, ⟨𝟙 _, Category.comp_id _⟩,
    ⟨Scheme.Modules.pullbackUnitIso _⟩, ⟨?_⟩⟩
  exact Scheme.Modules.pullbackUnitIso _ ≪≫ (Scheme.Modules.pullbackTensorUnitObjIso _).symm

p2m_export "AezTensorPow" "unit"
theorem main {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) := by
  induction n with
  | zero => exact unit a
  | succ n ih =>
    rw [Scheme.Modules.tensorPow_succ]
    exact ih.tensor hL

end AezTensorPow

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard in
theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)} {L : A.Modules}
    (hL : IsAlgEquivZero a L) (n : ℕ) : IsAlgEquivZero a (L.tensorPow n) :=
  AezTensorPow.main hL n

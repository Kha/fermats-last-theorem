import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_tensor_tensorPow_iso_tensorPow_of_iso_of_iso_unit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory"

noncomputable def tensorPowCongr {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') : ∀ n : ℕ, L.tensorPow n ≅ L'.tensorPow n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowCongr e n) e

noncomputable def unitTensorPow {X : Scheme.{u}} : ∀ d : ℕ, (𝟙_ X.Modules).tensorPow d ≅ 𝟙_ X.Modules
  | 0 => Iso.refl _
  | d + 1 => tensorIso (unitTensorPow d) (Iso.refl _) ≪≫ λ_ (𝟙_ X.Modules)

theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) (A B : Y.Modules) (ℒ : X.Modules) (n d : ℕ)
    (hA : Nonempty ((Scheme.Modules.pullback g).obj A ≅ ℒ))
    (hB : Nonempty ((Scheme.Modules.pullback g).obj B ≅ 𝟙_ X.Modules)) :
    Nonempty ((Scheme.Modules.pullback g).obj (A.tensorPow n ⊗ B.tensorPow d) ≅ ℒ.tensorPow n) := by
  obtain ⟨eA⟩ := hA
  obtain ⟨eB⟩ := hB
  obtain ⟨pA⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso g A n
  obtain ⟨pB⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso g B d
  exact ⟨Scheme.Modules.pullbackTensorObjIso g (A.tensorPow n) (B.tensorPow d) ≪≫
    tensorIso (pA ≪≫ tensorPowCongr eA n) (pB ≪≫ tensorPowCongr eB d ≪≫ unitTensorPow d) ≪≫ ρ_ (ℒ.tensorPow n)⟩

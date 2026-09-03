import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_tensorPow_mul_iso

universe u

p2m_open "CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory"

set_option autoImplicit false

namespace TensorPowMulSol

noncomputable def tensorPowAdd {X : Scheme.{u}} (L : X.Modules) (a : ℕ) :
    (b : ℕ) → (L.tensorPow (a + b) ≅ L.tensorPow a ⊗ L.tensorPow b)
  | 0 => (ρ_ _).symm
  | b + 1 => (tensorPowAdd L a b ⊗ᵢ Iso.refl L) ≪≫ α_ _ _ _

noncomputable def tensorPowMul {X : Scheme.{u}} (L : X.Modules) (a : ℕ) :
    (b : ℕ) → (L.tensorPow (a * b) ≅ (L.tensorPow a).tensorPow b)
  | 0 => Iso.refl _
  | b + 1 => tensorPowAdd L (a * b) a ≪≫ (tensorPowMul L a b ⊗ᵢ Iso.refl _)

end TensorPowMulSol

theorem solution {X : Scheme.{u}} (L : X.Modules) (a b : ℕ) :
    Nonempty (L.tensorPow (a * b) ≅ (L.tensorPow a).tensorPow b) :=
  ⟨TensorPowMulSol.tensorPowMul L a b⟩

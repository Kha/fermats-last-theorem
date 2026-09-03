import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import P2M.Util
namespace P2MW.S_ModularForm_mdifferentiable_slash_heckeDiagMatrix

theorem solution (d : ℕ) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (SlashAction.map k (ModularForm.heckeDiagMatrix d) f) :=
  MDifferentiable.slash hf k (ModularForm.heckeDiagMatrix d)

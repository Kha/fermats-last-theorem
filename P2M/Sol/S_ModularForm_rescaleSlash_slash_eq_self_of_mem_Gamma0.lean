import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import P2M.Util
namespace P2MW.S_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0

open scoped ModularForm

theorem solution {R M d : ℕ} [NeZero M]
    (hdRM : d * R ∣ M) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (SlashAction.map k (ModularForm.heckeDiagMatrix d) f)
      = SlashAction.map k (ModularForm.heckeDiagMatrix d) f :=
  FreyPackage.ModMCarrier.rescaleSlash_slash hdRM k hf hγ

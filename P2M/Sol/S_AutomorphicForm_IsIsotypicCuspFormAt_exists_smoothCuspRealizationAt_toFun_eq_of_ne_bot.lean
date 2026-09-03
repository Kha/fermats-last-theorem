import Definitions.Def_AutomorphicForm_CuspidalConstituent
import P2M.Util
namespace P2MW.S_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : IsIsotypicCuspFormAt F pins ξ N S Ψ φ) (h0 : φ ≠ 0) :
    ∃ (Ψ' : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Ψ'.toRawCentral),
      Ψ'.level = N ∧ (∀ v, Ψ'.a v = Ψ.a v) ∧ (∀ v, Ψ'.b v = Ψ.b v) ∧
        R.toFun = φ ∧ R.centralChar = ξ ∧ R.exceptionalSet = S := by
  refine ⟨⟨N, hN, Ψ.a, Ψ.b⟩, ?_, rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  · exact
      { toFun := φ
        exists_ne_zero := Function.ne_iff.mp h0
        centralChar := ξ
        smoothCusp := h.smoothCusp
        level_invariant := h.level_invariant
        exceptionalSet := S
        hecke_eigen := h.hecke_eigen
        central_eigen := h.central_eigen }
  · exact ⟨rfl, rfl, rfl⟩

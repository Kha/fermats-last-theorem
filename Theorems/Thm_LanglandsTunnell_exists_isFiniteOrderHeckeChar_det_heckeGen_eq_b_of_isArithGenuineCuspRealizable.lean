import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HeckeCharacter_FiniteOrder
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open HeckeIntegralSeam

theorem LanglandsTunnell.exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) Φ)
    (n : ℕ) (hn : 0 < n) (hbn : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, Φ.b v ^ n = 1) :
    ∃ η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, HeckeCharacter.IsFiniteOrderHeckeChar F η ∧
      (∃ 𝔣 : Ideal (𝓞 F), 𝔣 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus F η 𝔣) ∧
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        ((η (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) : ℂˣ) : ℂ) = Φ.b v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_isFiniteOrderHeckeChar_det_heckeGen_eq_b_of_isArithGenuineCuspRealizable.solution

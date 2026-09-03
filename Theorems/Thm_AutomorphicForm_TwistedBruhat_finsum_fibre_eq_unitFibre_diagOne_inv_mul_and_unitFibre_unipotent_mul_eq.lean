import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq
attribute [-instance] NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped Pointwise

theorem AutomorphicForm.TwistedBruhat.finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ) :
    (∀ (e : Lˣ) (a : L), a * σ (e : L) = (e : L) →
      ∀ (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = a},
            φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ * g)) =
          ∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
            φ (((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ *
                ((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)))) ∧
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = a},
                φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * g) =
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                φ (((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g)⁻¹ *
                  AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * ((AutomorphicForm.globalPoints (𝓞 L) L (diagOne e))⁻¹ * g))) ∧
    (∀ (l : L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
        (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
            φ ((AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g)⁻¹ *
              AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ *
                (AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g))) =
          ∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
            (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
            φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L ζ * g))) ∧
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                φ ((AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g)⁻¹ *
                  AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * (AutomorphicForm.globalPoints (𝓞 L) L (AutomorphicForm.unipotentGL2 l) * g)) =
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
            (@AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
              (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
                φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TwistedBruhat_finsum_fibre_eq_unitFibre_diagOne_inv_mul_and_unitFibre_unipotent_mul_eq.solution

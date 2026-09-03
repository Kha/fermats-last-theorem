import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import P2M.Util
import P2M.Sol.S_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward

theorem AutomorphicForm.TwistedBruhat.finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (x q : AdeleRing (𝓞 L) L) (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : AdelicGL2 (𝓞 L) L) :
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k))) =
      ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
        φ (k⁻¹ *
          unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) *
            ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k)) ∧
    (∑ᶠ δ ∈ {δ : GL (Fin 2) L |
        (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = 1},
        φ ((unipotentGL2 x * diagOne t * k)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (unipotentGL2 q * (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * k)))) =
      ∑ᶠ b : L,
        φ (k⁻¹ *
          unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + D.act σ q + actSubId K L D σ x) *
            ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_TwistedBruhat_finsum_unitFibre_iwasawa_eq_finsum_trace_ne_zero_and_finsum_unitFibre_unipotent_eq_finsum.solution

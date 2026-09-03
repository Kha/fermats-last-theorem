import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_coupled_one_of_forall_integral_centralizer_eq_mul_of_forall_integral_twistedCentralizer_eq_mul

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.coupled_one_of_forall_integral_centralizer_eq_mul_of_forall_integral_twistedCentralizer_eq_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (cτ : ℝ) (hcτ : 0 < cτ)
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hγδ : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) γ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    [τ.IsHaarMeasure]
    (hτ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (s : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂τ =
        cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)) [τ'.IsHaarMeasure]
    (hτ' : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
      ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ' =
        cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νZK.prod νZK)) :
    AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ γ δ 1 τ τ' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_coupled_one_of_forall_integral_centralizer_eq_mul_of_forall_integral_twistedCentralizer_eq_mul.solution

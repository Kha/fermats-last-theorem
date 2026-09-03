import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ₀ : GL (Fin 2) K) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (a : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN : LT.TwistedNorm.IsNormRep σ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀) δ₀)
    (hc : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hy : AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ
      (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
        AutomorphicForm.centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) y) :
    ∃ e : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃ₜ*
        Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
      (∀ t, AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)
          ((e t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
            Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) : AutomorphicForm.AdelicGL2 (𝓞 K) K) =
        y⁻¹ * (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * y) ∧
      (∀ t, ((e t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
            Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) : AutomorphicForm.AdelicGL2 (𝓞 K) K) ∈
          (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) K))).map (AutomorphicForm.globalPoints (𝓞 K) K) ↔
        (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          (AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))) ∧
      (∀ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
          AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u)} :
          Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ
          (AutomorphicForm.globalPoints (𝓞 K) K γ₀ *
            AutomorphicForm.centralScalar (𝓞 K) K
              (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a * u))
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) y τ
          (@Measure.map _ _ _
            (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c))
            e.symm τ)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_continuousMulEquiv_twistedCentralizer_centralizer_coupled_of_isNormRep.solution

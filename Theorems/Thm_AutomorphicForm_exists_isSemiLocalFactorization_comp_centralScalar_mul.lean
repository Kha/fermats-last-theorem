import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isSemiLocalFactorization_comp_centralScalar_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      AutomorphicForm.IsSemiLocalFactorization K L S₁
        (fun g => φ (AutomorphicForm.centralScalar (𝓞 L) L z * g))
        (fun y => φa (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleArch (𝓞 L) L).toMonoidHom z) * y))
        (fun h => φf (Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z) * h))
        (fun v x => (if v ∈ S then φS v
            else (AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
          (Matrix.GeneralLinearGroup.scalar (Fin 2)
            (Units.map (AutomorphicForm.semiLocalEval K L v).toMonoidHom
              (Units.map (AdelicLevel.adeleFin (𝓞 L) L).toMonoidHom z)) * x)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSemiLocalFactorization_comp_centralScalar_mul.solution

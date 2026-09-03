import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isUnitFactorization_comp_centralScalar_mul

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_isUnitFactorization_comp_centralScalar_mul
    (K : Type) [Field K] [NumberField K]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      AutomorphicForm.IsUnitFactorization K S₁
        (fun g => f (AutomorphicForm.centralScalar (𝓞 K) K z * g))
        (fun y => fa (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) * y))
        (fun h => ff (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z) * h))
        (fun v x => (if v ∈ S then fS v
            else (AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
          (AdelicLevel.finComponent (𝓞 K) K v
            (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z)) * x)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isUnitFactorization_comp_centralScalar_mul.solution

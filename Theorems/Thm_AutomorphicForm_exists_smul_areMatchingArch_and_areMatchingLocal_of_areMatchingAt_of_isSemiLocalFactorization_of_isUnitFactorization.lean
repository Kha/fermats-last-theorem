import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct in

theorem AutomorphicForm.exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (hm : AutomorphicForm.AreMatchingAt K L σ S φ f)

    (hφ0 : ∃ g, φ g ≠ 0) (hf0 : ∃ g, f g ≠ 0) :
    ∃ (ρa : ℂ) (ρ : HeightOneSpectrum (𝓞 K) → ℂ),
      ρa ≠ 0 ∧ (∀ v ∈ S, ρ v ≠ 0) ∧ ρa * ∏ v ∈ S, ρ v = 1 ∧
      AutomorphicForm.IsArchTestFactor K (ρa • fa) ∧ (∀ v ∈ S, AutomorphicForm.IsLocalTestFn K v (ρ v • fS v)) ∧
      AutomorphicForm.AreMatchingArch K L σ φa (ρa • fa) ∧
      ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (ρ v • fS v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_smul_areMatchingArch_and_areMatchingLocal_of_areMatchingAt_of_isSemiLocalFactorization_of_isUnitFactorization.solution

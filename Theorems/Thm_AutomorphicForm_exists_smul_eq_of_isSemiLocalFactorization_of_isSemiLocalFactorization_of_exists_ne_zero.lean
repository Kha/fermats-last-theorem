import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open scoped TensorProduct in

theorem AutomorphicForm.exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (φa' : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ' : AutomorphicForm.IsSemiLocalFactorization K L S φ φa' φf' φS')
    (h0 : ∃ g, φ g ≠ 0) :
    ∃ (ca : ℂ) (c : HeightOneSpectrum (𝓞 K) → ℂ),
      ca ≠ 0 ∧ (∀ v ∈ S, c v ≠ 0) ∧ ca * ∏ v ∈ S, c v = 1 ∧
      φa' = ca • φa ∧ ∀ v ∈ S, φS' v = c v • φS v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_smul_eq_of_isSemiLocalFactorization_of_isSemiLocalFactorization_of_exists_ne_zero.solution

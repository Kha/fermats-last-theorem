import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_smul_eq_of_isUnitFactorization_of_isUnitFactorization_of_exists_ne_zero
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.exists_smul_eq_of_isUnitFactorization_of_isUnitFactorization_of_exists_ne_zero
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff' : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS' : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf' : AutomorphicForm.IsUnitFactorization K S f fa' ff' fS')
    (h0 : ∃ g, f g ≠ 0) :
    ∃ (da : ℂ) (d : HeightOneSpectrum (𝓞 K) → ℂ),
      da ≠ 0 ∧ (∀ v ∈ S, d v ≠ 0) ∧ da * ∏ v ∈ S, d v = 1 ∧
      fa' = da • fa ∧ ∀ v ∈ S, fS' v = d v • fS v := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_smul_eq_of_isUnitFactorization_of_isUnitFactorization_of_exists_ne_zero.solution

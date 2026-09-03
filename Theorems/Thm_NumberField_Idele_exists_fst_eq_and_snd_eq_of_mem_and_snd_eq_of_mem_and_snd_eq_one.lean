import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.Idele.exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one
    (K : Type) [Field K] [NumberField K]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) :
    ∃ zs : (AdeleRing (𝓞 K) K)ˣ,
      ((zs : AdeleRing (𝓞 K) K).1 = (z : AdeleRing (𝓞 K) K).1) ∧
      (∀ v ∈ S, (zs : AdeleRing (𝓞 K) K).2 v = (z : AdeleRing (𝓞 K) K).2 v) ∧
      (∀ v ∈ T, v ∉ S → (zs : AdeleRing (𝓞 K) K).2 v = ((x v : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → (zs : AdeleRing (𝓞 K) K).2 v = 1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one.solution

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped Topology

theorem NumberField.AdelicLevel.exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one
    (K : Type) [Field K] [NumberField K]
    (V : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (_hV : V ∈ 𝓝 (1 : GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (e : ℕ),
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), glArch (𝓞 K) K g = 1 →
        (∀ (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2),
          ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K ∧
          (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
            ∈ v.adicCompletionIntegers K) →
        (∀ v ∈ T, ∀ i j : Fin 2,
          Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ)) ∧
          Valued.v ((((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v
              - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(e : ℤ))) →
        g ∈ V := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_exists_finset_forall_mem_of_valued_sub_le_of_mem_nhds_one.solution

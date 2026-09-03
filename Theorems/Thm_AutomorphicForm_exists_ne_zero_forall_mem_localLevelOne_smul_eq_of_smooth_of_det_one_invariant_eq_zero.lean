import Mathlib.RepresentationTheory.Basic
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ne_zero_forall_mem_localLevelOne_smul_eq_of_smooth_of_det_one_invariant_eq_zero

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_ne_zero_forall_mem_localLevelOne_smul_eq_of_smooth_of_det_one_invariant_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin 2) (v.adicCompletion K)) W)
    (hW : ∃ w : W, w ≠ 0)
    (hsmooth : ∀ w : W, ∃ m : ℕ, ∀ g : GL (Fin 2) (v.adicCompletion K),
      (∀ i j : Fin 2, Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j - (1 : Matrix (Fin 2) (Fin 2)
        (v.adicCompletion K)) i j) ≤ AdelicLevel.idealBound (𝓞 K) (v.asIdeal ^ m) v) → ρ g w = w)
    (hsl : ∀ w : W,
      (∀ h : GL (Fin 2) (v.adicCompletion K), (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 1 → ρ h w = w) →
      w = 0) :
    ∃ (c : ℕ) (w : W), w ≠ 0 ∧
      ∀ g ∈ AdelicDock.localLevelOne (𝓞 K) K v (v.asIdeal ^ c), ρ g w = w := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ne_zero_forall_mem_localLevelOne_smul_eq_of_smooth_of_det_one_invariant_eq_zero.solution

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem AutomorphicForm.exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (c : (v.adicCompletion K)ˣ) (n : ℕ) (hn : 0 < n) :
    ∀ V' ∈ nhds (1 : GL (Fin 2) (v.adicCompletion K)),
      ∃ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
        ∀ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ →
          ∃ β : GL (Fin 2) (v.adicCompletion K), β ∈ V' ∧
            (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈
              Algebra.adjoin (v.adicCompletion K) {(γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))} ∧
            β ^ n = (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_forall_exists_pow_eq_of_isRegularSemisimple.solution

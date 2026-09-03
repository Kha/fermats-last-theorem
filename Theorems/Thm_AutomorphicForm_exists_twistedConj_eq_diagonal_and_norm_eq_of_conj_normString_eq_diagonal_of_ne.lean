import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem AutomorphicForm.exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (L : Type) [Field L] [NumberField L] [Algebra K L] (w : v.Extension (𝓞 L))
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (α β : (v.adicCompletion K)ˣ) (hαβ : α ≠ β) (δ y : GL (Fin 2) (w.1.adicCompletion L))
    (hy : ((y⁻¹ *
      ((List.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))).map
          fun i : ℕ => Matrix.GeneralLinearGroup.map (θ ^ i).toAlgHom.toRingHom δ).prod *
        y : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      !![algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K), 0;
        0, algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K)]) :
    ∃ (x : GL (Fin 2) (w.1.adicCompletion L)) (a b : (w.1.adicCompletion L)ˣ),
      ((x⁻¹ * δ * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x :
            GL (Fin 2) (w.1.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
          !![(a : w.1.adicCompletion L), 0; 0, (b : w.1.adicCompletion L)] ∧
        (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (α : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (a : w.1.adicCompletion L)) ∧
        (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (β : v.adicCompletion K) =
      ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (b : w.1.adicCompletion L)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_twistedConj_eq_diagonal_and_norm_eq_of_conj_normString_eq_diagonal_of_ne.solution

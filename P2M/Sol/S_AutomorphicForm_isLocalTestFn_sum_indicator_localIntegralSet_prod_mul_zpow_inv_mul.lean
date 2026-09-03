import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
namespace P2MW.S_AutomorphicForm_isLocalTestFn_sum_indicator_localIntegralSet_prod_mul_zpow_inv_mul

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (v.adicCompletion K)) (z : GL (Fin 2) (v.adicCompletion K)) (k j : ℕ) :
    AutomorphicForm.IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
      ∑ ι : Fin k → Fin n, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x))  := by
  classical

  have hmul : ∀ (g : GL (Fin 2) (v.adicCompletion K)) {f : GL (Fin 2) (v.adicCompletion K) → ℂ},
      AutomorphicForm.IsLocalTestFn K v f → AutomorphicForm.IsLocalTestFn K v (fun x => f (g * x)) :=
    fun g f h => ⟨h.1.comp_continuous (continuous_const_mul g), h.2.comp_homeomorph (Homeomorph.mulLeft g)⟩
  have hadd : ∀ {f g : GL (Fin 2) (v.adicCompletion K) → ℂ}, AutomorphicForm.IsLocalTestFn K v f →
      AutomorphicForm.IsLocalTestFn K v g → AutomorphicForm.IsLocalTestFn K v (fun x => f x + g x) :=
    fun hf hg => ⟨(hf.1.prodMk hg.1).comp (fun p : ℂ × ℂ => p.1 + p.2), hf.2.add hg.2⟩
  have hsum : ∀ (s : Finset (Fin k → Fin n)),
      AutomorphicForm.IsLocalTestFn K v (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι ∈ s, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
          (((List.ofFn fun i => rT (ι i)).prod * z ^ j)⁻¹ * x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using AutomorphicForm.isLocalTestFn_zero K v
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact hadd (hmul _ (AutomorphicForm.isLocalTestFn_indicator_localIntegralSet K v)) ih
  exact hsum Finset.univ

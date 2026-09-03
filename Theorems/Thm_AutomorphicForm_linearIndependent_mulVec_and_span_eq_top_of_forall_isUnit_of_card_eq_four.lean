import Definitions.Def_AutomorphicForm_BaseChangePlaces
import P2M.Util
import P2M.Sol.S_AutomorphicForm_linearIndependent_mulVec_and_span_eq_top_of_forall_isUnit_of_card_eq_four

set_option autoImplicit false

theorem AutomorphicForm.linearIndependent_mulVec_and_span_eq_top_of_forall_isUnit_of_card_eq_four
    (K L : Type) [Field K] [Field L] [Algebra K L] (h2 : Module.finrank K L = 2)
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L)
    (ι : Type) [Fintype ι] (hcard : Fintype.card ι = 4)
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hspan : ∀ x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ↔
        x ∈ Submodule.span K (Set.range b))
    (hdiv : ∀ x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ → x ≠ 0 → IsUnit x)
    (v : Fin 2 → L) (hv : v ≠ 0) :
    LinearIndependent K (fun i => (b i).mulVec v) ∧
      Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_linearIndependent_mulVec_and_span_eq_top_of_forall_isUnit_of_card_eq_four.solution

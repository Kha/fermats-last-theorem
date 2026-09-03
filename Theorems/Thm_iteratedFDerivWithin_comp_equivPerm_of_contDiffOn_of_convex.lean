import Mathlib
import P2M.Util
import P2M.Sol.S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex

set_option autoImplicit false

theorem iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : Convex ℝ s) (hs' : (interior s).Nonempty)
    {n : ℕ} {f : E → F} (hf : ContDiffOn ℝ n f s) {x : E} (hx : x ∈ s)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n f s x (v ∘ σ) = iteratedFDerivWithin ℝ n f s x v := by p2m_exact_reverting @_root_.P2MW.S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex.solution

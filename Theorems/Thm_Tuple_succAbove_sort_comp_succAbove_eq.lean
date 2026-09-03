import Mathlib
import P2M.Util
import P2M.Sol.S_Tuple_succAbove_sort_comp_succAbove_eq

set_option autoImplicit false
theorem Tuple.succAbove_sort_comp_succAbove_eq
    {n : ℕ} {ι : Type*} [LinearOrder ι] (u : Fin (n + 1) → ι) (hu : Function.Injective u) (i : Fin (n + 1)) (k : Fin n) :
    i.succAbove (Tuple.sort (u ∘ i.succAbove) k) = Tuple.sort u (((Tuple.sort u).symm i).succAbove k) := by p2m_exact_reverting @_root_.P2MW.S_Tuple_succAbove_sort_comp_succAbove_eq.solution

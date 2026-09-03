import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq

set_option autoImplicit false
theorem NumberField.InfinitePlace.isUnramifiedIn_of_pow_eq
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty) (u : E) (α : M) (hα : α ^ p = algebraMap E M u)
    (hgen : IntermediateField.adjoin E {α} = ⊤)
    (w : NumberField.InfinitePlace E)
    (hb : w.IsReal → ∃ b : w.Completion, algebraMap E w.Completion u = b ^ p) :
    w.IsUnramifiedIn M := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_isUnramifiedIn_of_pow_eq.solution

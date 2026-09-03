import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne

set_option autoImplicit false

open scoped IntermediateField

theorem LaurentSeries.algebraIsSeparable_adjoin_simple_of_forall_pow_ne
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (F : IntermediateField k (LaurentSeries k)) (t : ↥F)
    (htr : Transcendental k t) (hp : ∀ v : LaurentSeries k, v ^ p ≠ (t : LaurentSeries k))
    [FiniteDimensional ↥k⟮t⟯ ↥F] :
    Algebra.IsSeparable ↥k⟮t⟯ ↥F := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id

set_option autoImplicit false

universe u

theorem Algebra.FormallySmooth.linearIndepOn_pow_of_linearIndepOn_id
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.FormallySmooth k K]
    (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_linearIndepOn_pow_of_linearIndepOn_id.solution

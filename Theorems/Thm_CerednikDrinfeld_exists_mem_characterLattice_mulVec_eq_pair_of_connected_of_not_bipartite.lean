import Mathlib
import Definitions.Def_CerednikDrinfeld_Ribbon
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite

set_option autoImplicit false

open ModularCurve

theorem CerednikDrinfeld.exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] (a b : E → V)
    (hsymm : ∀ e : E, ∃ e' : E, a e' = b e ∧ b e' = a e)
    (hconn : ∀ P : Set V, (∀ e : E, a e ∈ P ↔ b e ∈ P) → P = ∅ ∨ P = Set.univ)
    (hodd : ∀ P : Set V, P.Nonempty → ∃ e : E, (a e ∈ P ↔ b e ∈ P))
    (x y : V → ℤ) (hx : x ∈ characterLattice V) (hy : y ∈ characterLattice V) :
    ∃ D : E → ℤ, D ∈ characterLattice E ∧
      (CerednikDrinfeld.degeneracyMatrix a).mulVec D = x ∧
      (CerednikDrinfeld.degeneracyMatrix b).mulVec D = y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_mem_characterLattice_mulVec_eq_pair_of_connected_of_not_bipartite.solution

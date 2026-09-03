import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_squarefree_of_squarefree_map

theorem Polynomial.squarefree_of_squarefree_map {κ L : Type*} [Field κ] [CommRing L] [IsDomain L]
    (φ : κ →+* L) {f : Polynomial κ} (hf : Squarefree (f.map φ)) : Squarefree f := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_squarefree_of_squarefree_map.solution

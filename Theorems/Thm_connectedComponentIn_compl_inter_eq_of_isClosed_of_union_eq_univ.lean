import Mathlib
import P2M.Util
import P2M.Sol.S_connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ

set_option autoImplicit false

theorem connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ∪ B = Set.univ) (hA' : IsPreconnected (A \ B)) {e : X} (he : e ∈ A \ B) :
    connectedComponentIn (A ∩ B)ᶜ e = A ∩ (A ∩ B)ᶜ := by p2m_exact_reverting @_root_.P2MW.S_connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ.solution

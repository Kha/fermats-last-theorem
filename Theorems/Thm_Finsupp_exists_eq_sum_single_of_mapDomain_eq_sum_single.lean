import Mathlib
import P2M.Util
import P2M.Sol.S_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single

theorem Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single
    {α β : Type*} (f : α → β) (E : α →₀ ℤ) (hE : 0 ≤ E)
    {d : ℕ} (v : Fin d → β) (hv : Function.Injective v)
    (h : Finsupp.mapDomain f E = ∑ i, Finsupp.single (v i) (1 : ℤ)) :
    ∃ Q : Fin d → α, E = ∑ i, Finsupp.single (Q i) (1 : ℤ) ∧ ∀ i, f (Q i) = v i := by p2m_exact_reverting @_root_.P2MW.S_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single.solution

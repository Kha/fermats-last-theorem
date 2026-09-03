import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul

set_option autoImplicit false

theorem Matrix.span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul
    {G : Type*} [Group G] {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) F)
    (hodd : ∃ c : G, ρ c * ρ c = 1 ∧ (ρ c).det = -1)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ σ : G, ∀ c : F, (ρ σ).mulVec v ≠ c • v)
    {k : Type*} [Field k] (ι : F →+* k) :
    Submodule.span k (Set.range fun g : G => (ρ g).map ι) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_span_range_map_eq_top_of_exists_odd_of_forall_exists_mulVec_ne_smul.solution

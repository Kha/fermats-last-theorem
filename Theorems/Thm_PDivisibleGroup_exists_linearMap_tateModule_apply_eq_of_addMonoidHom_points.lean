import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points

set_option autoImplicit false

open scoped TensorProduct

theorem PDivisibleGroup.exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] {L : Type} [Field L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h') (F : G.Points L →+ H.Points L) :
    ∃ TF : TateModule p (G.Points L) →ₗ[ℤ_[p]] TateModule p (H.Points L),
      ∀ (x : TateModule p (G.Points L)) (n : ℕ),
        ((TF x : TateModule p (H.Points L)) : ℕ → H.Points L) n = F ((x : ℕ → G.Points L) n) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_apply_eq_of_addMonoidHom_points.solution

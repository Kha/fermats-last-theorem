import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff

set_option autoImplicit false

theorem PDivisibleGroup.exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} (G : PDivisibleGroup R p h) (k : ℕ)
    (T : G.CPoints (integralClosure R (PadicAlgCl p))) (hT : (p ^ k) • T = 0) :
    ∃ t : G.Point (integralClosure R (PadicAlgCl p)) k,
      G.toCPoints (integralClosure R (PadicAlgCl p))
        (G.pointsMkAdd (integralClosure R (PadicAlgCl p)) k (Additive.ofMul t)) = T := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff.solution

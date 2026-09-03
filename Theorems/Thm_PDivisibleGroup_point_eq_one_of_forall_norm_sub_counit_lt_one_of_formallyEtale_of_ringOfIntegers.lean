import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers

set_option autoImplicit false

theorem PDivisibleGroup.point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (Q : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) (v : ℕ) [Algebra.FormallyEtale (PadicAlgCl.ringOfIntegers p K) (Q.level v)]
    (g : Q.Point (PadicAlgCl p) v)
    (hg : ∀ a : Q.level v, ‖PDivisibleGroup.Point.toAlgHom g a -
      algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) :
    g = 1 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers.solution

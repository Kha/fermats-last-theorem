import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one

set_option autoImplicit false

theorem PDivisibleGroup.forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h h' : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) (Q : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h')
    (ψ : ∀ v : ℕ, Q.level v →ₐc[PadicAlgCl.ringOfIntegers p K] G.level v)
    (Tψ : TateModule p (G.Points (PadicAlgCl p)) →ₗ[ℤ_[p]] TateModule p (Q.Points (PadicAlgCl p)))
    (hTψ : ∀ (x : TateModule p (G.Points (PadicAlgCl p))) (n w : ℕ) (g : G.Point (PadicAlgCl p) w),
        G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) = (x : ℕ → G.Points (PadicAlgCl p)) n →
        ((Tψ x : TateModule p (Q.Points (PadicAlgCl p))) : ℕ → Q.Points (PadicAlgCl p)) n =
          Q.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (ψ w : Q.level w →ₐ[PadicAlgCl.ringOfIntegers p K] G.level w)))))
    (x : TateModule p (G.Points (PadicAlgCl p)))
    (hx : ∀ n : ℕ, ∃ (w : ℕ) (g : G.Point (PadicAlgCl p) w),
      G.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
        (x : ℕ → G.Points (PadicAlgCl p)) n ∧
      ∀ a : G.level w, ‖PDivisibleGroup.Point.toAlgHom g a -
        algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) :
    ∀ n : ℕ, ∃ (w : ℕ) (g : Q.Point (PadicAlgCl p) w),
      Q.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul g) =
        (Tψ x : ℕ → Q.Points (PadicAlgCl p)) n ∧
      ∀ a : Q.level w, ‖PDivisibleGroup.Point.toAlgHom g a -
        algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_forall_exists_norm_sub_counit_lt_one_map_of_forall_exists_norm_sub_counit_lt_one.solution

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (i w : ℕ)
    (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
      Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i}) w)
    (hf : ∀ a : G.level w,
      IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a)))
    (ψ : G'.Point (integralClosure R (PadicAlgCl p)) w)
    (hψ : ∀ z : G.Point (integralClosure R (PadicAlgCl p)) w,
      (∀ a : G.level w, PDivisibleGroup.Point.toAlgHom z a -
          algebraMap R (integralClosure R (PadicAlgCl p)) (Coalgebra.counit a) ∈
        (Ideal.span {(p : integralClosure R (PadicAlgCl p))}).radical) →
      D.pair (integralClosure R (PadicAlgCl p)) w z ψ = 1) :
    D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R
      (Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ i})) w ψ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff.solution

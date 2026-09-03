import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.bijective_tateModule_pairing_of_isAlgClosed
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (B : TateModule p (G.Points L) →ₗ[ℤ_[p]] TateModule p (G'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : ∀ (x : TateModule p (G.Points L)) (y : TateModule p (G'.Points L)) (v : ℕ)
      (f : G.Point L v) (ψ : G'.Point L v),
      G.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → G.Points L) v →
      G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v →
      ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f ψ) :
    Function.Bijective B.flip ∧ Function.Bijective B := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed.solution

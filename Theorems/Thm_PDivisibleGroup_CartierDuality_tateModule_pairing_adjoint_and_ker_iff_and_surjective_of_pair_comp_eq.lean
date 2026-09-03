import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq
    {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime]
    {A A' : PDivisibleGroup R p h} (D : A.CartierDuality A')
    {Γ Γ' : PDivisibleGroup R p h'} (E : Γ.CartierDuality Γ')
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (B : TateModule p (A.Points L) →ₗ[ℤ_[p]] TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : (∀ (x : TateModule p (A.Points L)) (y : TateModule p (A'.Points L)) (v : ℕ)
        (f : A.Point L v) (g : A'.Point L v),
        A.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → A.Points L) v →
        A'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → A'.Points L) v →
        ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f g))
    (BE : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (Γ'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hBE : (∀ (x : TateModule p (Γ.Points L)) (y : TateModule p (Γ'.Points L)) (v : ℕ)
        (f : Γ.Point L v) (g : Γ'.Point L v),
        Γ.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → Γ.Points L) v →
        Γ'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → Γ'.Points L) v →
        ((Additive.toMul ((BE x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = E.pair L v f g))
    (φ : ∀ v : ℕ, A.level v →ₐc[R] Γ.level v) (ψ : ∀ v : ℕ, Γ'.level v →ₐc[R] A'.level v)
    (hadj : ∀ (v : ℕ) (x : Γ.Point L v) (y : A'.Point L v),
      D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp
          (φ v : A.level v →ₐ[R] Γ.level v))) y =
        E.pair L v x (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp
          (ψ v : Γ'.level v →ₐ[R] A'.level v))))
    (Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (A.Points L))
    (hTφ : ∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (A.Points L)) : ℕ → A.Points L) n =
          A.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : A.level w →ₐ[R] Γ.level w)))))
    (Tψ : TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Γ'.Points L))
    (hTψ : ∀ (y : TateModule p (A'.Points L)) (n w : ℕ) (g : A'.Point L w),
        A'.pointsMkAdd L w (Additive.ofMul g) = (y : ℕ → A'.Points L) n →
        ((Tψ y : TateModule p (Γ'.Points L)) : ℕ → Γ'.Points L) n =
          Γ'.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (ψ w : Γ'.level w →ₐ[R] A'.level w))))) :
    (∀ (x : TateModule p (Γ.Points L)) (y : TateModule p (A'.Points L)), B (Tφ x) y = BE x (Tψ y)) ∧
    (∀ y : TateModule p (A'.Points L), Tψ y = 0 ↔ ∀ x : TateModule p (Γ.Points L), B (Tφ x) y = 0) ∧
    ((Function.Injective Tφ ∧
        ∀ (r : ℤ_[p]) (z : TateModule p (A.Points L)), r ≠ 0 → r • z ∈ LinearMap.range Tφ →
          z ∈ LinearMap.range Tφ) →
      Function.Surjective Tψ) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq.solution

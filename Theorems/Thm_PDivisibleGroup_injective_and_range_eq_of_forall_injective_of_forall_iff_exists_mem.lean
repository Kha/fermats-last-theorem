import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem

set_option autoImplicit false
theorem PDivisibleGroup.injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (Γ : PDivisibleGroup R p h')
    (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1)))
    (Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (G.Points L))
    (hTφ : ∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : G.level w →ₐ[R] Γ.level w)))))
    (M : Submodule ℤ_[p] (TateModule p (G.Points L)))
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points L)), r ≠ 0 → r • x ∈ M → x ∈ M)
    (hinj : ∀ v : ℕ, Function.Injective (fun g : Γ.Point L v =>
        PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom g).comp (φ v : G.level v →ₐ[R] Γ.level v)) :
          Γ.Point L v → G.Point L v))
    (himg : ∀ (v : ℕ) (y : G.Point L v),
        (∃ g : Γ.Point L v, PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ v : G.level v →ₐ[R] Γ.level v)) = y) ↔
          ∃ x ∈ M, G.pointsMkAdd L v (Additive.ofMul y) = (x : ℕ → G.Points L) v) :
    Function.Injective Tφ ∧ LinearMap.range Tφ = M := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_injective_and_range_eq_of_forall_injective_of_forall_iff_exists_mem.solution

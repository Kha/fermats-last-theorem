import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_submodule_annihilator_stable_saturated_and_forall_mem_iff

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.exists_submodule_annihilator_stable_saturated_and_forall_mem_iff
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {A A' : PDivisibleGroup R p h}
    (D : A.CartierDuality A') (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (B : TateModule p (A.Points L) →ₗ[ℤ_[p]] TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : (∀ (x : TateModule p (A.Points L)) (y : TateModule p (A'.Points L)) (v : ℕ)
        (f : A.Point L v) (g : A'.Point L v),
        A.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → A.Points L) v →
        A'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → A'.Points L) v →
        ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f g))
    (hBσ : ∀ (σ : L ≃ₐ[R] L) (x : TateModule p (A.Points L)) (y : TateModule p (A'.Points L)) (v : ℕ),
        ((Additive.toMul ((B (A.tateModuleRep L σ x) (A'.tateModuleRep L σ y) : ℕ → Additive Lˣ) v) : Lˣ) : L) =
          σ (((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L)))
    (M : Submodule ℤ_[p] (TateModule p (A'.Points L)))
    (hMstab : ∀ (σ : L ≃ₐ[R] L) (x : TateModule p (A'.Points L)), x ∈ M → A'.tateModuleRep L σ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (A'.Points L)), r ≠ 0 → r • x ∈ M → x ∈ M) :
    ∃ N : Submodule ℤ_[p] (TateModule p (A.Points L)),
      (∀ y : TateModule p (A.Points L), y ∈ N ↔ ∀ x ∈ M, B y x = 0) ∧
      (∀ (σ : L ≃ₐ[R] L) (y : TateModule p (A.Points L)), y ∈ N → A.tateModuleRep L σ y ∈ N) ∧
      (∀ (r : ℤ_[p]) (y : TateModule p (A.Points L)), r ≠ 0 → r • y ∈ N → y ∈ N) ∧
      (∀ x : TateModule p (A'.Points L), x ∈ M ↔ ∀ y ∈ N, B y x = 0) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_submodule_annihilator_stable_saturated_and_forall_mem_iff.solution

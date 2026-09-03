import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_existsUnique_algHom_apply_eq_of_isNilpotent

universe u v w

theorem Algebra.FormallySmooth.existsUnique_algHom_apply_eq_of_isNilpotent
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) {g : ℕ} (x : Fin g → A) (hx : ∀ i, e (x i) = 0)
    (hgen : RingHom.ker e ≤ Ideal.span (Set.range x) ⊔ RingHom.ker e ^ 2)
    (hind : ∀ c : Fin g → R, (∑ i, c i • x i) ∈ RingHom.ker e ^ 2 → c = 0)
    {C : Type w} [CommRing C] [Algebra R C] (J : Ideal C) (hJ : IsNilpotent J)
    (c : Fin g → C) (hc : ∀ i, c i ∈ J) :
    ∃! φ : A →ₐ[R] C, (∀ a : A, e a = 0 → φ a ∈ J) ∧ ∀ i, φ (x i) = c i := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_existsUnique_algHom_apply_eq_of_isNilpotent.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_finrank_eq_pow_of_isPullback_frobenius

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.finrank_eq_pow_of_isPullback_frobenius
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (pr : X' ⟶ X)
    (hpr : IsPullback pr f' f (Spec.map (CommRingCat.ofHom (frobenius k p))))
    (F : X ⟶ X') (hF : F ≫ f' = f)
    (hFrob : ∀ (B : Type u) [CommRing B] [CharP B p] (x : Spec (CommRingCat.of B) ⟶ X),
      x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x) :
    ∀ y : ↥X', F.finrank y = p ^ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_finrank_eq_pow_of_isPullback_frobenius.solution

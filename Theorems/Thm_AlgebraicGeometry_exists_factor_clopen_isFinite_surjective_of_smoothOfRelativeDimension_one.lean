import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_factor_clopen_isFinite_surjective_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_factor_clopen_isFinite_surjective_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {M XH : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 πM]
    (πXH : XH ⟶ Spec (CommRingCat.of k)) (πH : M ⟶ XH) (hπHX : πH ≫ πXH = πM) [IsFinite πH]
    (C₀ : M.Opens) (hC₀cl : IsClosed (C₀ : Set M)) (hC₀conn : _root_.IsConnected (C₀ : Set M))
    [IsIntegral (C₀ : Scheme.{u})]
    (U : XH.Opens) (hUcl : IsClosed (U : Set XH)) [IsIntegral (U : Scheme.{u})]
    [SmoothOfRelativeDimension 1 (U.ι ≫ πXH)]
    (x : M) (hx : x ∈ C₀) (hxU : πH.base x ∈ U) :
    ∃ c : (C₀ : Scheme.{u}) ⟶ (U : Scheme.{u}), c ≫ U.ι = C₀.ι ≫ πH ∧ IsFinite c ∧ Function.Surjective c.base := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_factor_clopen_isFinite_surjective_of_smoothOfRelativeDimension_one.solution

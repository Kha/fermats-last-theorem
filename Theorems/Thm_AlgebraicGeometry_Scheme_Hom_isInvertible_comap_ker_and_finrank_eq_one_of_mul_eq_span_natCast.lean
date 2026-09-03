import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast
    {O : Type u} [CommRing O] [IsLocalRing O] {p : ℕ}
    (h𝔪 : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {X : Scheme.{u}} (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ] (hker : σ.ker.IsInvertible)
    (J J' : X.IdealSheafData) [IsIntegral J.subscheme]
    (hprod : ∀ U : X.affineOpens, (J * J').ideal U = Ideal.span {((p : ℕ) : Γ(X, U))})
    (hJ' : σ.base (IsLocalRing.closedPoint O) ∉ J'.support)
    (hne : ∃ x ∈ J.support, x ∉ Set.range σ.base)
    {k : Type u} [Field k] (y : J.subscheme ⟶ Spec (CommRingCat.of k))
    (hrat : ∃ s : Spec (CommRingCat.of k) ⟶ J.subscheme,
      s ≫ y = 𝟙 _ ∧ σ.base (IsLocalRing.closedPoint O) ∈ Set.range (s ≫ J.subschemeι).base) :
    (σ.ker.comap J.subschemeι).IsInvertible ∧
      IsFinite ((σ.ker.comap J.subschemeι).subschemeι ≫ y) ∧
      ∀ q : Spec (CommRingCat.of k), ((σ.ker.comap J.subschemeι).subschemeι ≫ y).finrank q = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isInvertible_comap_ker_and_finrank_eq_one_of_mul_eq_span_natCast.solution

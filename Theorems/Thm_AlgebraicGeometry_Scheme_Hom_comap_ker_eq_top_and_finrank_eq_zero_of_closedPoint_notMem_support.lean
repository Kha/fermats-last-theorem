import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support
    {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}}
    (σ : Spec (CommRingCat.of O) ⟶ X) [IsClosedImmersion σ]
    (J : X.IdealSheafData) (hJ : σ.base (IsLocalRing.closedPoint O) ∉ J.support)
    {k : Type u} [Field k] (y : J.subscheme ⟶ Spec (CommRingCat.of k)) :
    σ.ker.comap J.subschemeι = ⊤ ∧
      (σ.ker.comap J.subschemeι).IsInvertible ∧
      IsFinite ((σ.ker.comap J.subschemeι).subschemeι ≫ y) ∧
      ∀ q : Spec (CommRingCat.of k), ((σ.ker.comap J.subschemeι).subschemeι ≫ y).finrank q = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_comap_ker_eq_top_and_finrank_eq_zero_of_closedPoint_notMem_support.solution

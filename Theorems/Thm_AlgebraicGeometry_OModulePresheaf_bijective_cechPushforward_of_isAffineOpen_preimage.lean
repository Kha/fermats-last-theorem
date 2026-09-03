import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.bijective_cechPushforward_of_isAffineOpen_preimage
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p] (K' : V'.OrderedAffineCover)
    (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent)
    (W : P.affineOpens) (hW : IsAffineOpen (p ⁻¹ᵁ W.1)) :
    (∀ x y : G.obj (p ⁻¹ᵁ W.1),
        (∀ j : K'.ι, G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x
          = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) y) → x = y) ∧
      ∀ c : (OModulePresheaf.cechPushforward p q K' G).obj W.1,
        ∃ x : G.obj (p ⁻¹ᵁ W.1), ∀ j : K'.ι,
          c.1 j = G.res (OModulePresheaf.cechPushforward.chart_le_preimage p K' W.1 j) x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.solution

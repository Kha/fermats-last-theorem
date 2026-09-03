import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem AlgebraicGeometry.eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    (σ σ' : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hσ' : σ' ≫ c = 𝟙 _)
    (hx : σ'.base (IsLocalRing.closedPoint A) = σ.base (IsLocalRing.closedPoint A))

    (hker : ∀ (U : X.Opens) (hU : σ.base (IsLocalRing.closedPoint A) ∈ U) (s : X.presheaf.obj (Opposite.op U)),
      (σ.stalkMap (IsLocalRing.closedPoint A)).hom (X.presheaf.germ U (σ.base (IsLocalRing.closedPoint A)) hU s) = 0 →
      (σ'.stalkMap (IsLocalRing.closedPoint A)).hom
        (X.presheaf.germ U (σ'.base (IsLocalRing.closedPoint A)) (by rw [hx]; exact hU) s) = 0) :
    σ = σ' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le.solution

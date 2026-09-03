import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_disjoint_range_support_ker_of_comp_eq_comp_spec_of_isFractionRing_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.disjoint_range_support_ker_of_comp_eq_comp_spec_of_isFractionRing_of_surjective
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {k : Type u} [Field k] (toκ : O →+* k) (hκ : Function.Surjective toκ)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {X Z W : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of O))
    (f : Z ⟶ X) [QuasiCompact f]
    (hf : ∃ f₀ : Z ⟶ Spec (CommRingCat.of k), f ≫ q = f₀ ≫ Spec.map (CommRingCat.ofHom toκ))
    (g : W ⟶ X)
    (hg : ∃ g₀ : W ⟶ Spec (CommRingCat.of T'), g ≫ q = g₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap O T'))) :
    Disjoint (Set.range g.base) (f.ker.support : Set X) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_disjoint_range_support_ker_of_comp_eq_comp_spec_of_isFractionRing_of_surjective.solution

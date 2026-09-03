import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one
    (k : Type) [Field k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    let e : ↥G := (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)
    letI : Algebra k (G.presheaf.stalk e) :=
      ((G.presheaf.germ ⊤ e trivial).hom.comp (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)).toAlgebra
    (∀ a : G.presheaf.stalk e, ∃ c : k, a - algebraMap k (G.presheaf.stalk e) c ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk e)) ∧
    ∀ φ : (G.presheaf.stalk e) →ₗ[k] k,
      (∀ a ∈ (IsLocalRing.maximalIdeal (G.presheaf.stalk e)) ^ 2, φ a = 0) →
      (∀ c : k, φ (algebraMap k (G.presheaf.stalk e) c) = 0) →
      ∃ D : Derivation k (G.presheaf.stalk e) (G.presheaf.stalk e),
        ∀ a : G.presheaf.stalk e, D a - algebraMap k (G.presheaf.stalk e) (φ a) ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk e) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_forall_exists_sub_algebraMap_mem_and_exists_derivation_stalk_one.solution

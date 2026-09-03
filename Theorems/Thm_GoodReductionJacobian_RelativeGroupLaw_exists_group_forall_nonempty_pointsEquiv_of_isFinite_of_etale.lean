import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {C : Scheme.{u}} (lev : C ⟶ A) [IsClosedImmersion lev] [IsFinite (lev ≫ f)] [Etale (lev ≫ f)]
    (hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∃ z : T ⟶ C, z ≫ lev = (L.one t).1)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (∃ z : T ⟶ C, z ≫ lev = x.1) → (∃ z : T ⟶ C, z ≫ lev = y.1) → ∃ z : T ⟶ C, z ≫ lev = (L.mul t x y).1) :
    ∃ (G : Type u) (_ : Group G) (_ : Finite G),
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
        ∃ e : G ≃ {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1},
          ∀ a b : G,
            ((e (a * b) : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f // ∃ z : _ ⟶ C, z ≫ lev = x.1}) :
                SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f) =
              L.mul (Spec.map (CommRingCat.ofHom sk)) (e a) (e b) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_group_forall_nonempty_pointsEquiv_of_isFinite_of_etale.solution

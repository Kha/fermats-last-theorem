import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing
    (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver s f) (hu : L.IsTorsionPoint s n u)
    (huniv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t f),
      L.IsTorsionPoint t n z → ∃! g : T ⟶ S, g ≫ u.1 = z.1) :
    ∃ (act : pullback f s ⟶ A),
      act ≫ f = pullback.fst f s ≫ f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (g : T ⟶ S)
          (hx : x.1 ≫ f = g ≫ s),
        pullback.lift x.1 g hx ≫ act =
          (L.mul t x ⟨g ≫ u.1, by rw [Category.assoc, u.2, ← hx, x.2]⟩).1) ∧
      ∃ (hsh : pullback.fst f s ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n),
        IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n) (pullback.fst f s) act hsh) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing.solution

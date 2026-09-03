import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_isTorsionPoint_of_comp_eq
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    {T : Scheme.{u}} [PreconnectedSpace T] (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : G.IsTorsionPoint t n x) (hy : G.IsTorsionPoint t n y)
    {Z : Scheme.{u}} [Nonempty Z] (p : Z ⟶ T) (hp : p ≫ x.1 = p ≫ y.1) :
    x = y := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq.solution

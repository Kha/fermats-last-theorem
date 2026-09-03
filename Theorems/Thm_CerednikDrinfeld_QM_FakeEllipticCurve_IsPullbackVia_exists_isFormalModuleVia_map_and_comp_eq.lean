import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.QM.FakeEllipticCurve.IsPullbackVia.exists_isFormalModuleVia_map_and_comp_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q)
    (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    (E : FakeEllipticCurve Λ N B) (E' : FakeEllipticCurve Λ N B') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B B') E E' g)
    (X : FormalODModule q B) (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hX : E.IsFormalModuleVia coord X θ) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates E'.f 2, E'.IsFormalModuleVia coord (X.map (algebraMap B B')) θ' ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra B' B''] [IsScalarTower B B' B''] (s : Fin 2 → B''),
        (∀ i, IsNilpotent (s i)) → (θ' B'' s).1 ≫ g = (θ B'' s).1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsPullbackVia_exists_isFormalModuleVia_map_and_comp_eq.solution

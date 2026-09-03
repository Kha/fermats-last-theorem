import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_fstHom_comp_eq_of_isPullbackVia_map_smul_of_levelIff

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_fstHom_comp_eq_of_isPullbackVia_map_smul_of_levelIff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    (k : Type) [Field k]
    (u : FakeEllipticCurve.WithFullLevel Λ N m k)
    (v w : FakeEllipticCurve.WithFullLevel Λ N m (DualNumber k)) (c : k)
    (gv : u.1.A ⟶ v.1.A) (hgv : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom v.1 u.1 gv)
    (hgvP : (u.2.P).1 ≫ gv = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (v.2.P).1)
    (h : w.1.A ⟶ v.1.A)
    (hh : FakeEllipticCurve.IsPullbackVia
      (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v.1 w.1 h)
    (hhP : (w.2.P).1 ≫ h =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ (v.2.P).1)

    (hhlev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P : SchemeHomOver t' w.1.f),
      (∃ P₀ : T ⟶ v.1.C, P₀ ≫ v.1.lev = P.1 ≫ h) → FactorsThrough w.1.lev P) :
    ∃ gw : u.1.A ⟶ w.1.A,
      FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w.1 u.1 gw ∧
      (u.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (w.2.P).1 ∧
      gw ≫ h = gv := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_fstHom_comp_eq_of_isPullbackVia_map_smul_of_levelIff.solution

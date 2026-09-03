import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_torsionBasis_pushPt_act_of_neZero

set_option autoImplicit false
universe u
open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.torsionBasis_pushPt_act_of_neZero
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ) [NeZero m] (P : E.FullLevel m)
    (e : Fin 4 → ↥Λ)
    (hgen : ∀ x : ↥Λ, ∃ n : Fin 4 → ℤ, x = ∑ i, n i • e i)
    (hind : ∀ n : Fin 4 → ℤ, ∑ i, n i • e i = 0 → n = 0) :
      let Pe : Fin 4 → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f :=
        fun i => pushPt (E.act (e i)) (E.act_over (e i)) P.P

      (∀ i : Fin 4, nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m (Pe i) = E.L.one (𝟙 (Spec (CommRingCat.of S)))) ∧

      (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k),
        (∀ R : SchemeHomOver (geomPoint k sk) E.f, nsmulPt E.L (geomPoint k sk) m R = E.L.one (geomPoint k sk) →
          ∃ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 3)) = R) ∧
        (∀ n : Fin 4 → ℕ,
            E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk) (E.L.mul (geomPoint k sk)
              (nsmulPt E.L (geomPoint k sk) (n 0) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 0)) (nsmulPt E.L (geomPoint k sk) (n 1) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 1)))
              (nsmulPt E.L (geomPoint k sk) (n 2) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 2))) (nsmulPt E.L (geomPoint k sk) (n 3) ((fun i => FakeEllipticCurve.sectionAt (Pe i) k sk) 3)) = E.L.one (geomPoint k sk) →
          ∀ i : Fin 4, m ∣ n i)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_torsionBasis_pushPt_act_of_neZero.solution

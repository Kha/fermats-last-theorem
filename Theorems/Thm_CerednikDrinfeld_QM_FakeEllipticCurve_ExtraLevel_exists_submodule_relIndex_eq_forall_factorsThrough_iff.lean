import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_relIndex_eq_forall_factorsThrough_iff

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_relIndex_eq_forall_factorsThrough_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (hm : (m : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (P : E.FullLevel m) (ℓ : ℕ) (hℓm : ℓ ∣ m) (K : E.ExtraLevel ℓ) :
    ∃ L : Submodule ℤ ℍ[ℚ, a, b], L ≤ Λ ∧ (∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L) ∧
      (∀ (y : ↥Λ) (x : ℍ[ℚ, a, b]), x ∈ L → (y : ℍ[ℚ, a, b]) * x ∈ L) ∧
      L.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧
      ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (sk : k →+* k') (Q : SchemeHomOver (geomPoint k' sk) E.f),
        FactorsThrough K.levK Q ↔
          ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L ∧
            pushPt (E.act x) (E.act_over x)
              (nsmulPt E.L (geomPoint k' sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k' sk)) = Q := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_relIndex_eq_forall_factorsThrough_iff.solution

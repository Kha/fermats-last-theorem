import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type} [CommRing S] (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) [NeZero ℓ]
    (W : ZMod ℓ × ZMod ℓ → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (hW_add : ∀ i j : ZMod ℓ × ZMod ℓ, W (i + j) = E.L.mul (𝟙 (Spec (CommRingCat.of S))) (W i) (W j))
    (hW_stable : ∀ (x : ↥Λ) (i : ZMod ℓ × ZMod ℓ), ∃ j : ZMod ℓ × ZMod ℓ, pushPt (E.act x) (E.act_over x) (W i) = W j)
    (hW_inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i j : ZMod ℓ × ZMod ℓ),
      FakeEllipticCurve.sectionAt (W i) k sk = FakeEllipticCurve.sectionAt (W j) k sk → i = j)
    (hW_lev : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (i : ZMod ℓ × ZMod ℓ),
      FactorsThrough E.lev (FakeEllipticCurve.sectionAt (W i) k sk) → i = 0) :
    ∃ K : E.ExtraLevel ℓ,
      (∀ i : ZMod ℓ × ZMod ℓ, FactorsThrough K.levK (W i)) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
        FactorsThrough K.levK Q ↔ ∃ i : ZMod ℓ × ZMod ℓ, FakeEllipticCurve.sectionAt (W i) k sk = Q := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_exists_sectionAt_eq.solution

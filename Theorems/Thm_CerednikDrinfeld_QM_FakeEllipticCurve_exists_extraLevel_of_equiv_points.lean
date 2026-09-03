import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points
attribute [-simp] NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_of_equiv_points
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ}
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k)
    (S : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (e : ZMod ℓ × ZMod ℓ ≃ S)
    (he : ∀ x y : ZMod ℓ × ZMod ℓ,
      ((e (x + y) : S) : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
        E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y))
    (hstab : ∀ (m : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f),
      P ∈ S → pushPt (E.act m) (E.act_over m) P ∈ S)
    (hdisj : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f,
      P ∈ S → FactorsThrough E.lev P → P = E.L.one (𝟙 (Spec (CommRingCat.of k)))) :
    ∃ K : E.ExtraLevel ℓ,
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough K.levK P ↔ P ∈ S := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_of_equiv_points.solution

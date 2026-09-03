import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.exists_zmod_mul_prod_equiv_factorsThrough_of_coprime
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N ℓ : ℕ) (hNℓ : N.Coprime ℓ)
    (S : Type) [CommRing S] (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    {C' : Scheme.{0}} (lev' : C' ⟶ u.1.A)
    (hlev' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough lev' P ↔
        FactorsThrough u.1.lev (nsmulPt u.1.L t ℓ P) ∧ FactorsThrough u.2.levK (nsmulPt u.1.L t N P))
    (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (hk : ((N * ℓ : ℕ) : k) ≠ 0) :
    ∃ e : ZMod (N * ℓ) × ZMod (N * ℓ) ≃ {P : SchemeHomOver (geomPoint k sk) u.1.f // FactorsThrough lev' P},
      ∀ x y : ZMod (N * ℓ) × ZMod (N * ℓ),
        (e (x + y) : SchemeHomOver (geomPoint k sk) u.1.f) = u.1.L.mul (geomPoint k sk) (e x) (e y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_exists_zmod_mul_prod_equiv_factorsThrough_of_coprime.solution

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_nsmul_pushPt_act_eq_one_and_finComb_injective_and_exists_finComb_eq

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.nsmul_pushPt_act_eq_one_and_finComb_injective_and_exists_finComb_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ) [NeZero m] (FL : E.FullLevel m)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j) :
    (∀ i : Fin (2 * 2), E.L.nsmul (𝟙 (Spec (CommRingCat.of S))) m (pushPt (E.act (β i)) (E.act_over (β i)) FL.P) = E.L.one (𝟙 (Spec (CommRingCat.of S)))) ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (c c' : Fin (2 * 2) → Fin m),
      E.L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (pushPt (E.act (β i)) (E.act_over (β i)) FL.P)) (fun i => (c i : ℕ)) =
        E.L.finComb (Spec.map (CommRingCat.ofHom sk))
          (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (pushPt (E.act (β i)) (E.act_over (β i)) FL.P)) (fun i => (c' i : ℕ)) →
        c = c') ∧
    (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) E.f),
      E.L.nsmul (Spec.map (CommRingCat.ofHom sk)) m Q = E.L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * 2) → Fin m,
          E.L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (pushPt (E.act (β i)) (E.act_over (β i)) FL.P)) (fun i => (c i : ℕ)) = Q) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_nsmul_pushPt_act_eq_one_and_finComb_injective_and_exists_finComb_eq.solution

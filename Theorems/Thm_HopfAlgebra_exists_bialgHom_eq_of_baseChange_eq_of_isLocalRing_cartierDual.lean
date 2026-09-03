import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
attribute [-instance] Deformation.TruncWitt.instSubsingleton Deformation.DieudonneModule.instInhabited Deformation.wittHomShiftLE_directedSystem Deformation.DieudonneModule.instAddCommGroup
attribute [-simp] Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec Deformation.wittHomDieudonneDatum_F_apply Deformation.TruncWitt.shift_truncate Deformation.coe_wittHomShift Deformation.coe_wittHomFrobenius Deformation.wittHomDieudonneDatum_V_apply Deformation.TruncWitt.coeff_map Deformation.coe_wittHomVerschiebung Deformation.coe_wittHomRestrict Deformation.coe_wittHomMap Deformation.TruncWitt.map_truncate Deformation.TruncWitt.coeff_frobeniusFun Deformation.TruncWitt.verschiebung_truncate Deformation.TruncWitt.map_id Deformation.TruncWitt.shiftLE_refl Deformation.DieudonneModule.dieudonneDatum_F_apply Deformation.coe_wittHomShiftLE Deformation.DieudonneModule.frobenius_of Deformation.DieudonneModule.lift_of Deformation.TruncWitt.verschiebungIter_apply Deformation.DieudonneModule.map_of Deformation.DieudonneModule.dieudonneDatum_V_apply Deformation.DieudonneModule.of_shift Deformation.TruncWitt.shiftLE_truncate Deformation.DieudonneModule.verschiebung_of Deformation.DieudonneModule.of_shiftLE Deformation.wittHomShiftLE_refl

universe u v w w'

theorem HopfAlgebra.exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] (hunif : Irreducible (p : O))
    (k : Type v) [Field k] [Algebra O k] (hk : Function.Surjective (algebraMap O k))
    (hker : RingHom.ker (algebraMap O k) = Ideal.span {(p : O)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra O ℛ] [Module.Finite O ℛ] [Module.Free O ℛ]
    (H : Type w') [CommRing H] [HopfAlgebra O H] [Coalgebra.IsCocomm O H]
    [Module.Finite O H] [Module.Free O H] (hrank : ∃ a : ℕ, Module.finrank O H = p ^ a)
    (hunip : IsLocalRing (CartierDual k (TensorProduct O k H)))
    (ψ : TensorProduct O k H →ₐc[k] TensorProduct O k ℛ)
    (x : H →ₐ[O] ℛ)
    (hx : Algebra.TensorProduct.map (AlgHom.id k k) x =
      (ψ : TensorProduct O k H →ₐ[k] TensorProduct O k ℛ)) :
    ∃ Φ : H →ₐc[O] ℛ, (Φ : H →ₐ[O] ℛ) = x := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_eq_of_baseChange_eq_of_isLocalRing_cartierDual.solution

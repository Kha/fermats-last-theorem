import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem CerednikDrinfeld.FormalODModule.exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (Φ : FormalODModule p B) (N : ℕ)
    [Module.Finite B (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    [Module.Free B (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N)))]
    (hX : ∀ i, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N)))) (MvPowerSeries.X i))) :
    ∃ (L : Type) (_ : CommRing L) (_ : HopfAlgebra B L) (_ : Coalgebra.IsCocomm B L)
      (_ : Module.Free B L) (_ : Module.Finite B L) (π : MvPowerSeries (Fin 2) B →ₐ[B] L),
      Function.Surjective π ∧
      RingHom.ker π = Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N))) ∧
      Module.finrank B L = Module.finrank B (FormalODModule.KerAlgebra (Φ.act ((p : Zp2 p) ^ N))) ∧
      (∀ i, IsNilpotent (π (MvPowerSeries.X i))) ∧
      (∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G) ∧
      (∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (Φ.F.toPowerSeries i)) ∧
      (∀ i, Coalgebra.counit (R := B) (π (MvPowerSeries.X i)) = 0) ∧
      (∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G) ∧
      (∀ a : Zp2 p, ∃ ρ : L →ₐc[B] L, ∀ G, ρ (π G) = π (MvPowerSeries.subst (Φ.act a) G)) ∧
      (∃ ϖ : L →ₐc[B] L, ∀ G, ϖ (π G) = π (MvPowerSeries.subst Φ.varpi G)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_hopfAlgebra_ker_eq_span_act_pow_and_forall_bialgHom_subst_act.solution

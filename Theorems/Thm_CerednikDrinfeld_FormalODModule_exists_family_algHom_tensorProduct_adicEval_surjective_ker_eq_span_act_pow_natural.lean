import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem CerednikDrinfeld.FormalODModule.exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural
    (p : ℕ) [Fact p.Prime] {B₀ : Type} [CommRing B₀] (Φ : FormalODModule p B₀) (N : ℕ)
    (L : Type) [CommRing L] [HopfAlgebra B₀ L]
    (π : MvPowerSeries (Fin 2) B₀ →ₐ[B₀] L) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span (Set.range (Φ.act ((p : Zp2 p) ^ N))))
    (hX : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hΔ : ∀ i, Coalgebra.comul (R := B₀) (π (MvPowerSeries.X i)) =
      MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B₀] L))
        (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B₀] (1 : L)) (fun j => (1 : L) ⊗ₜ[B₀] π (MvPowerSeries.X j)))
        (Φ.F.toPowerSeries i))
    (hε : ∀ G, Coalgebra.counit (R := B₀) (π G) = MvPowerSeries.constantCoeff G)
    (ρ : Zp2 p → (L →ₐc[B₀] L)) (hρ : ∀ a G, ρ a (π G) = π (MvPowerSeries.subst (Φ.act a) G))
    (ϖ : L →ₐc[B₀] L) (hϖ : ∀ G, ϖ (π G) = π (MvPowerSeries.subst Φ.varpi G)) :
    ∃ θ : ∀ (S : Type) [CommRing S] [Algebra B₀ S], MvPowerSeries (Fin 2) S →ₐ[S] S ⊗[B₀] L,
      (∀ (S : Type) [CommRing S] [Algebra B₀ S],
        (∀ i, θ S (MvPowerSeries.X i) = (1 : S) ⊗ₜ[B₀] π (MvPowerSeries.X i)) ∧
        (∀ G, θ S G = MvFormalGroup.adicEval (⊥ : Ideal (S ⊗[B₀] L)) (fun i => (1 : S) ⊗ₜ[B₀] π (MvPowerSeries.X i)) G) ∧
        Function.Surjective (θ S) ∧
        RingHom.ker (θ S) = Ideal.span (Set.range ((Φ.map (algebraMap B₀ S)).act ((p : Zp2 p) ^ N))) ∧
        (∀ i, Coalgebra.comul (R := S) (θ S (MvPowerSeries.X i)) =
          MvFormalGroup.adicEval (⊥ : Ideal ((S ⊗[B₀] L) ⊗[S] (S ⊗[B₀] L)))
            (Sum.elim (fun j => θ S (MvPowerSeries.X j) ⊗ₜ[S] (1 : S ⊗[B₀] L))
              (fun j => (1 : S ⊗[B₀] L) ⊗ₜ[S] θ S (MvPowerSeries.X j)))
            ((Φ.map (algebraMap B₀ S)).F.toPowerSeries i)) ∧
        (∀ G, Coalgebra.counit (R := S) (θ S G) = MvPowerSeries.constantCoeff G) ∧
        (∀ (a : Zp2 p) (G : MvPowerSeries (Fin 2) S),
          Algebra.TensorProduct.map (AlgHom.id S S) (ρ a : L →ₐ[B₀] L) (θ S G) =
            θ S (MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act a) G)) ∧
        (∀ G : MvPowerSeries (Fin 2) S,
          Algebra.TensorProduct.map (AlgHom.id S S) (ϖ : L →ₐ[B₀] L) (θ S G) =
            θ S (MvPowerSeries.subst (Φ.map (algebraMap B₀ S)).varpi G)) ∧
        (∀ G : MvPowerSeries (Fin 2) S,
          HopfAlgebra.antipode S (A := S ⊗[B₀] L) (θ S G) =
            θ S (MvPowerSeries.subst ((Φ.map (algebraMap B₀ S)).act (-1)) G))) ∧
      (∀ (S S' : Type) [CommRing S] [CommRing S'] [Algebra B₀ S] [Algebra B₀ S'] (f : S →ₐ[B₀] S')
        (G : MvPowerSeries (Fin 2) S),
        Algebra.TensorProduct.map f (AlgHom.id B₀ L) (θ S G) = θ S' (MvPowerSeries.map (f : S →+* S') G)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_family_algHom_tensorProduct_adicEval_surjective_ker_eq_span_act_pow_natural.solution

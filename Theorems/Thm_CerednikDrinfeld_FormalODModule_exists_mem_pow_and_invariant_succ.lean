import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_mem_pow_and_invariant_succ

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem CerednikDrinfeld.FormalODModule.exists_mem_pow_and_invariant_succ
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (X : FormalODModule p B) (I : Ideal (MvPowerSeries (Fin 2) B))
    (hnil : ∃ q : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q ∈ I)
    (hmul : ∀ f ∈ I, MvPowerSeries.subst X.F.toPowerSeries f ∈
      Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) '' (I : Set (MvPowerSeries (Fin 2) B))))
    {L : Type} [CommRing L] [HopfAlgebra B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (hcomul : ∀ i, Coalgebra.comul (R := B) (π (MvPowerSeries.X i)) =
        MvFormalGroup.adicEval (⊥ : Ideal (L ⊗[B] L))
          (Sum.elim (fun j => π (MvPowerSeries.X j) ⊗ₜ[B] (1 : L)) (fun j => (1 : L) ⊗ₜ[B] π (MvPowerSeries.X j)))
          (X.F.toPowerSeries i))
    (hcounit : ∀ G, Coalgebra.counit (R := B) (π G) = MvPowerSeries.constantCoeff G)
    [Module.Free B L] [Module.Finite B L]
    (N : ℕ) (hN : N ≠ 0)
    (δ : (MvPowerSeries (Fin 2) B ⧸ I ^ N) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L)
    (hδ : ∀ G, δ (Ideal.Quotient.mk (I ^ N) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ N) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ N) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : (MvPowerSeries (Fin 2) B ⧸ I ^ N)) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (δ' : (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) →ₐ[B] (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) ⊗[B] L)
    (hδ' : ∀ G, δ' (Ideal.Quotient.mk (I ^ (N + 1)) G) =
        MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) ⊗[B] L))
          (fun i => MvFormalGroup.adicEval (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1)) ⊗[B] L))
            (Sum.elim (fun j => Ideal.Quotient.mk (I ^ (N + 1)) (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
              (fun j => (1 : (MvPowerSeries (Fin 2) B ⧸ I ^ (N + 1))) ⊗ₜ[B] π (MvPowerSeries.X j)))
            (X.F.toPowerSeries i)) G)
    (f : MvPowerSeries (Fin 2) B) (hf : f ∈ I)
    (hinv : δ (Ideal.Quotient.mk (I ^ N) f) = Ideal.Quotient.mk (I ^ N) f ⊗ₜ[B] (1 : L)) :
    ∃ s : MvPowerSeries (Fin 2) B, s ∈ I ^ N ∧
      δ' (Ideal.Quotient.mk (I ^ (N + 1)) (f - s)) = Ideal.Quotient.mk (I ^ (N + 1)) (f - s) ⊗ₜ[B] (1 : L) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_mem_pow_and_invariant_succ.solution

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_map_mkQ_adicEval_sumElim_tmul_eq_zero_iff_mem_span_image_subst

set_option autoImplicit false

open scoped TensorProduct

theorem MvFormalGroup.map_mkQ_adicEval_sumElim_tmul_eq_zero_iff_mem_span_image_subst
    {S : Type} [CommRing S] {C : Type} [CommRing C] [Algebra S C]
    (θ : MvPowerSeries (Fin 2) S →ₐ[S] C) (hθ : Function.Surjective θ)
    (hX : ∀ i, IsNilpotent (θ (MvPowerSeries.X i)))
    (hev : ∀ G, θ G = MvFormalGroup.adicEval (⊥ : Ideal C) (fun i => θ (MvPowerSeries.X i)) G)
    (I : Ideal (MvPowerSeries (Fin 2) S)) (hI : RingHom.ker θ ≤ I)
    (G : MvPowerSeries (Fin 2 ⊕ Fin 2) S) :
    TensorProduct.map ((I.map θ).restrictScalars S).mkQ ((I.map θ).restrictScalars S).mkQ
        (MvFormalGroup.adicEval (⊥ : Ideal (C ⊗[S] C))
          (Sum.elim (fun j => θ (MvPowerSeries.X j) ⊗ₜ[S] (1 : C)) (fun j => (1 : C) ⊗ₜ[S] θ (MvPowerSeries.X j))) G) = 0 ↔
      G ∈ Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
            (I : Set (MvPowerSeries (Fin 2) S)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
            (I : Set (MvPowerSeries (Fin 2) S))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_map_mkQ_adicEval_sumElim_tmul_eq_zero_iff_mem_span_image_subst.solution

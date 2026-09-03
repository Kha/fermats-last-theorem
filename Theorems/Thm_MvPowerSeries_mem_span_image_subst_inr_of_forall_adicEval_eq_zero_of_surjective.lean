import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_MvPowerSeries_mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

theorem MvPowerSeries.mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective
    {B : Type} [CommRing B]
    (I : Ideal (MvPowerSeries (Fin 2) B)) (hI : I.FG)
    {L : Type} [CommRing L] [Algebra B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (G : MvPowerSeries (Fin 2 ⊕ Fin 2) B)
    (hG : ∀ n : ℕ,
      MvFormalGroup.adicEval
        (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸
          (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))) ^ (n + 1)) ⊗[B] L))
        (Sum.elim
          (fun j => Ideal.Quotient.mk
            ((Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))) ^ (n + 1))
              (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
          (fun j => (1 : MvPowerSeries (Fin 2) B ⧸
            (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))) ^ (n + 1)) ⊗ₜ[B]
              π (MvPowerSeries.X j))) G = 0) :
    G ∈ Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective.solution

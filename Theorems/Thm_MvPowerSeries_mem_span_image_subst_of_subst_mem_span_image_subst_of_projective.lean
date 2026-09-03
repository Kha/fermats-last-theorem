import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_mem_span_image_subst_of_subst_mem_span_image_subst_of_projective

set_option autoImplicit false

p2m_open "MvPowerSeries~isNoetherianRing_fin_of_isNoetherianRing"

theorem MvPowerSeries.mem_span_image_subst_of_subst_mem_span_image_subst_of_projective
    {B : Type} [CommRing B] [IsNoetherianRing B] {q : ℕ} (I : Ideal (MvPowerSeries (Fin q) B))
    (hfin : Module.Finite B (MvPowerSeries (Fin q) B ⧸ I))
    (hproj : Module.Projective B (MvPowerSeries (Fin q) B ⧸ I))
    {d n m : ℕ} (a : Fin n → MvPowerSeries (Fin m) B) (ha0 : ∀ k, MvPowerSeries.constantCoeff (a k) = 0)
    (hinj : ∀ H : MvPowerSeries (Fin n ⊕ Fin d) B,
      MvPowerSeries.subst
          (Sum.elim (fun k => MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin m ⊕ Fin d) B)) (a k))
            (fun t => MvPowerSeries.X (Sum.inr t))) H = 0 → H = 0)
    (V : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B)
    (hV : MvPowerSeries.subst
        (Sum.elim (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin m) B))
          (fun k => MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inr j) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin m) B)) (a k))) V ∈
      Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin m) B))) ''
          (I : Set (MvPowerSeries (Fin q) B)))) :
    V ∈ Ideal.span ((MvPowerSeries.subst
        (fun l => (MvPowerSeries.X (Sum.inl (Sum.inr l)) : MvPowerSeries ((Fin d ⊕ Fin q) ⊕ Fin n) B))) ''
          (I : Set (MvPowerSeries (Fin q) B))) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_mem_span_image_subst_of_subst_mem_span_image_subst_of_projective.solution

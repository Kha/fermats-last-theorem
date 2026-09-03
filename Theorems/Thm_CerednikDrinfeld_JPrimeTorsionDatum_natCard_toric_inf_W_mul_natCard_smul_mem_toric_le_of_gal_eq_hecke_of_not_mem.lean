import Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_mul_natCard_smul_mem_toric_le_of_gal_eq_hecke_of_not_mem

set_option autoImplicit false
open ModularCurve CerednikDrinfeld

theorem CerednikDrinfeld.JPrimeTorsionDatum.natCard_toric_inf_W_mul_natCard_smul_mem_toric_le_of_gal_eq_hecke_of_not_mem
    {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    (Dm : JPrimeTorsionDatum p E V A)
    (q' : ℕ) (hq' : q'.Prime)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    (htoric : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hφsub : ∀ t : Dm.T, t ∈ Dm.toric →
      Dm.gal φ t = Dm.hecke ((q' : HeckeAlg) * heckeGen ⟨q', hq'⟩) t)
    (hφquot : ∀ t : Dm.T, Dm.gal φ t - Dm.hecke (heckeGen ⟨q', hq'⟩) t ∈ Dm.toric)
    (hincong : ((q' : HeckeAlg) - 1) * heckeGen ⟨q', hq'⟩ ∉ 𝔪) :
    Nat.card ↥(Dm.toric ⊓ Dm.W 𝔪) *
        Nat.card {t : Dm.T // ∀ x ∈ 𝔪, Dm.hecke x t ∈ Dm.toric} ≤
      Nat.card ↥(Dm.W 𝔪) * Nat.card ↥Dm.toric := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_mul_natCard_smul_mem_toric_le_of_gal_eq_hecke_of_not_mem.solution

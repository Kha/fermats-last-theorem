import Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
import Definitions.Def_ModularCurve_HeckeModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_eq_pow_finrank_quotient

set_option autoImplicit false
open CerednikDrinfeld ModularCurve

theorem CerednikDrinfeld.JPrimeTorsionDatum.natCard_toric_inf_W_eq_pow_finrank_quotient
    {p : ℕ} [Fact p.Prime] {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    (Dm : JPrimeTorsionDatum p E V A)
    (htor : ∀ (x : HeckeAlg) (t : Dm.T), t ∈ Dm.toric → Dm.hecke x t ∈ Dm.toric)
    (hlaw : ∀ (ℓ : Nat.Primes) (t : Dm.T) (ht : t ∈ Dm.toric) (hℓt : Dm.hecke (heckeGen ℓ) t ∈ Dm.toric),
      Dm.toricEquiv ⟨Dm.hecke (heckeGen ℓ) t, hℓt⟩ = (Dm.toricEquiv ⟨t, ht⟩) ∘ₗ heckeKernelMap Dm.H ℓ)
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hp : (p : HeckeAlg) ∈ 𝔪)
    {Y : Type} [AddCommGroup Y] [Module HeckeAlg Y]
    (eY : Y ≃+ ↥(ribbonKernel Dm.D))
    (hY : ∀ (ℓ : Nat.Primes) (m : Y), eY (heckeGen ℓ • m) = heckeKernelMap Dm.H ℓ (eY m)) :
    Nat.card ↥(Dm.toric ⊓ Dm.W 𝔪) =
      Nat.card (HeckeAlg ⧸ 𝔪) ^ Module.finrank (HeckeAlg ⧸ 𝔪) (Y ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Y))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_JPrimeTorsionDatum_natCard_toric_inf_W_eq_pow_finrank_quotient.solution

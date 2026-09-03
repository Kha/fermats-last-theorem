import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_OmegaNr_exists_isTwistedAct_iff_exists_even_isPullback

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.OmegaNr.exists_isTwistedAct_iff_exists_even_isPullback
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))
    (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (P P' : DeligneDatum (K := K₀) π B) :
    (∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) (ψ, P) (ψ, P')) ↔
      ∃ γ' ∈ Γ', DeligneDatum.IsPullback (K := K₀) (π := π) B (σ γ')⁻¹ P P' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_OmegaNr_exists_isTwistedAct_iff_exists_even_isPullback.solution

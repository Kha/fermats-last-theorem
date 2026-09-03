import Definitions.Def_CohCarrier_Inst
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open CohCarrier

theorem CohCarrier.exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime
    (M q : ℕ) [NeZero M] [NeZero q] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod (M * q))ˣ)
    (hH' : ∀ v : (ZMod (M * q))ˣ, v ∈ H' ↔ ZMod.unitsMap (dvd_mul_right M q) v ∈ H)
    (h1 : CohCarrier.LevelLE M (M * q) H H' 1)
    (𝒪 : Type) [CommRing 𝒪] :
    haveI : NeZero (M * q) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne q)⟩
    ∃ (u : (ZMod (M * q))ˣ) (w : Module.End 𝒪 (CohCarrier.H1 (M * q) H' 𝒪)),

      (ZMod.unitsMap (dvd_mul_right M q) u : ZMod M) * (q : ZMod M) = 1 ∧

      w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        (CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.heckeTL M H 𝒪 q -
            CohCarrier.heckeTL (M * q) H' 𝒪 q ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1) ∘ₗ
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧

      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        ((q : 𝒪) + 1) • LinearMap.id ∧

      CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ w ∘ₗ CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        CohCarrier.heckeTL M H 𝒪 q *
          CohCarrier.diamondL M H 𝒪 (ZMod.unitsMap (dvd_mul_right M q) u) ∧

      CohCarrier.iDegL M (M * q) H H' 1 𝒪 𝒪 h1 ∘ₗ CohCarrier.jDegL M (M * q) H H' 1 𝒪 𝒪 h1 =
        LinearMap.id + CohCarrier.heckeTL (M * q) H' 𝒪 q * w ∧

      w * w = CohCarrier.diamondL (M * q) H' 𝒪 u ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ≠ q →
        w * (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL (M * q) H' 𝒪 ℓ) * w) ∧
      (∀ v : (ZMod (M * q))ˣ,
        w * CohCarrier.diamondL (M * q) H' 𝒪 v = CohCarrier.diamondL (M * q) H' 𝒪 v * w) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_atkinLehnerOp_iDegL_jDegL_five_identities_of_prime.solution

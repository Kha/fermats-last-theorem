import Mathlib
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le
attribute [-simp] HeckeCohomology.coe_heckeInv HeckeCohomology.heckeZ1Lin_apply

set_option autoImplicit false

open CongruenceSubgroup

theorem CohCarrier.exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le
    (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) (S₀ : Set ℕ)
    (hN4 : 4 ≤ N)
    (κ : Type) [Field κ] (hq1 : (q : κ) + 1 = 0) (h2 : (2 : κ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    (ρ : Representation κ (CuspidalType.GL2 q) V)
    (π : ↥(CuspidalType.steinberg q κ).toSubmodule →ₗ[κ] V)
    (hπ : ∀ g : CuspidalType.GL2 q, ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule,
      π ⟨CuspidalType.ind q κ g v, (CuspidalType.steinberg q κ).apply_mem_toSubmodule g v.2⟩ = ρ g (π v))
    (hπsurj : Function.Surjective π)
    (hπker : ∀ v : ↥(CuspidalType.steinberg q κ).toSubmodule, π v = 0 ↔ ∃ c : κ, (v : CuspidalType.ProjLine q →₀ κ) = c • CuspidalType.constFun q κ)
    (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (ρ.comp ((Matrix.SpecialLinearGroup.toGL.comp
            (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)))).comp (Gamma0 N).subtype))
      (fun ℓ : ℕ =>
        if h : ((ℓ : ZMod q) ≠ 0) then ρ (CuspidalType.diagElem q (Units.mk0 (ℓ : ZMod q) h)) else LinearMap.id)
      (insert q S₀) lam) :
    haveI : NeZero (N * q) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : q.Prime).ne_zero⟩
    (∃ v : CohCarrier.H1 (N * q) ⊥ κ, v ≠ 0 ∧
      (∀ σ : CongruenceSubgroup.Gamma0 (N * q), CohCarrier.diamondRaw (N * q) ⊥ κ σ v = v) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N * q → ℓ ∉ S₀ →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CohCarrier.heckeT (N * q) ⊥ ℓ κ v = lam ℓ • v) ∨
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ insert q S₀ → lam ℓ = (ℓ : κ) + 1 := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_diamondRaw_eq_heckeT_eq_smul_gammaH_bot_mul_or_eisenstein_of_isEigensystemH1_of_steinberg_quotient_of_four_le.solution

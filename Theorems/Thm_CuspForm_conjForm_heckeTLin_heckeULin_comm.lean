import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_conjForm_heckeTLin_heckeULin_comm
set_option autoImplicit false

theorem CuspForm.conjForm_heckeTLin_heckeULin_comm (N : ℕ) [NeZero N] (k : ℤ)
    (ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hρ : ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane),
      ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩)) :
    (∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k),
        ρ (CuspForm.heckeTLin k hℓ hℓN f) = CuspForm.heckeTLin k hℓ hℓN (ρ f)) ∧
      (∀ {q : ℕ} (hqN : q ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k),
        ρ (CuspForm.heckeULin k hqN f) = CuspForm.heckeULin k hqN (ρ f)) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_conjForm_heckeTLin_heckeULin_comm.solution

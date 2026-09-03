import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor

set_option autoImplicit false

theorem MvFormalGroup.CartierModule.exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    {B B₀ B₁ B₀₁ : Type} [CommRing B] [CommRing B₀] [CommRing B₁] [CommRing B₀₁]
    (q₀ : B →+* B₀) (q₁ : B →+* B₁) (r₀ : B₀ →+* B₀₁) (r₁ : B₁ →+* B₀₁)
    (hsq : r₀.comp q₀ = r₁.comp q₁)
    (hinj : ∀ b : B, q₀ b = 0 → q₁ b = 0 → b = 0)
    (hglue : ∀ (b₀ : B₀) (b₁ : B₁), r₀ b₀ = r₁ b₁ → ∃ b : B, q₀ b = b₀ ∧ q₁ b = b₁)
    (Φ : MvFormalGroup d B) [Φ.IsComm]
    (Φ₀ : MvFormalGroup d B₀) [Φ₀.IsComm] (h₀ : Φ.map q₀ = Φ₀)
    (Φ₁ : MvFormalGroup d B₁) [Φ₁.IsComm] (h₁ : Φ.map q₁ = Φ₁)
    (Ψ : MvFormalGroup d B₀₁) [Ψ.IsComm] (h₀' : Φ₀.map r₀ = Ψ) (h₁' : Φ₁.map r₁ = Ψ) :
    (∀ m : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.baseChangeEq q₀ h₀ m = 0 →
        MvFormalGroup.CartierModule.baseChangeEq q₁ h₁ m = 0 → m = 0) ∧
    (∀ (m₀ : MvFormalGroup.CartierModule p Φ₀) (m₁ : MvFormalGroup.CartierModule p Φ₁),
        MvFormalGroup.CartierModule.baseChangeEq r₀ h₀' m₀ = MvFormalGroup.CartierModule.baseChangeEq r₁ h₁' m₁ →
        ∃ m : MvFormalGroup.CartierModule p Φ,
          MvFormalGroup.CartierModule.baseChangeEq q₀ h₀ m = m₀ ∧
          MvFormalGroup.CartierModule.baseChangeEq q₁ h₁ m = m₁) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_baseChangeEq_eq_and_of_baseChangeEq_eq_of_milnor.solution

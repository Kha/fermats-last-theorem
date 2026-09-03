import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.so3Triple_typeOne_ker_identities_and_decomposition
    {V : Type*} [AddCommGroup V] [Module ℂ V] (F : Submodule ℂ V) [FiniteDimensional ℂ F] (J₁ J₂ J₃ : Module.End ℂ V)
    (hF₁ : ∀ f ∈ F, J₁ f ∈ F) (hF₂ : ∀ f ∈ F, J₂ f ∈ F) (hF₃ : ∀ f ∈ F, J₃ f ∈ F)
    (h12 : ∀ f ∈ F, J₁ (J₂ f) - J₂ (J₁ f) = J₃ f)
    (h23 : ∀ f ∈ F, J₂ (J₃ f) - J₃ (J₂ f) = J₁ f)
    (h31 : ∀ f ∈ F, J₃ (J₁ f) - J₁ (J₃ f) = J₂ f)
    (hcas : ∀ f ∈ F, J₁ (J₁ f) + J₂ (J₂ f) + J₃ (J₃ f) = (-2 : ℂ) • f)
    (B : V → V → ℂ)
    (hlin : ∀ (z : ℂ), ∀ w₁ ∈ F, ∀ w₂ ∈ F, ∀ w' ∈ F, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hsymm : ∀ w ∈ F, ∀ w' ∈ F, B w' w = (starRingEnd ℂ) (B w w'))
    (hpos : ∀ w ∈ F, w ≠ 0 → 0 < (B w w).re)
    (hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))
    (hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))
    (hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y)) :
    (∀ h ∈ F, J₃ h = 0 → J₁ (J₁ h) = -h ∧ J₂ (J₂ h) = -h ∧ J₁ (J₂ h) = 0 ∧ J₂ (J₁ h) = 0) ∧
    (∀ x ∈ F, J₃ (J₂ (J₃ (J₃ x))) = 0 ∧ J₃ (J₁ (J₃ (J₃ x))) = 0 ∧ J₃ (x + J₃ (J₃ x)) = 0 ∧
      x = J₂ (J₂ (J₃ (J₃ x))) + J₁ (J₁ (J₃ (J₃ x))) + (x + J₃ (J₃ x))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition.solution

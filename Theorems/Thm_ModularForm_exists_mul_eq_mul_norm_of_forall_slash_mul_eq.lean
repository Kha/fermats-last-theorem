import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq

set_option autoImplicit false

open scoped ModularForm

theorem ModularForm.exists_mul_eq_mul_norm_of_forall_slash_mul_eq
    (𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] {k : ℤ}
    (F G : ModularForm 𝒢 k)
    (hFG : ∀ h ∈ ℋ, ((⇑F : UpperHalfPlane → ℂ) ∣[k] h) * (⇑G : UpperHalfPlane → ℂ) =
      (⇑F : UpperHalfPlane → ℂ) * ((⇑G : UpperHalfPlane → ℂ) ∣[k] h)) :
    ∃ Φ : ModularForm ℋ (k * Nat.card (ℋ ⧸ 𝒢.subgroupOf ℋ)),
      (⇑Φ : UpperHalfPlane → ℂ) * (⇑G : UpperHalfPlane → ℂ) =
        (⇑F : UpperHalfPlane → ℂ) * (⇑(ModularForm.norm ℋ G) : UpperHalfPlane → ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_mul_eq_mul_norm_of_forall_slash_mul_eq.solution

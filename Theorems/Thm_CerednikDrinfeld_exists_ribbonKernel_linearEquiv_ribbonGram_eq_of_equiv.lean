import Definitions.Def_CerednikDrinfeld_Ribbon
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [DecidableEq V₁] [Fintype E₂] [DecidableEq V₂]
    (D₁ : DegeneracyData E₁ V₁) (D₂ : DegeneracyData E₂ V₂)
    (eE : E₁ ≃ E₂) (eV : V₁ ≃ V₂)
    (ha : ∀ e, D₂.a (eE e) = eV (D₁.a e)) (hb : ∀ e, D₂.b (eE e) = eV (D₁.b e)) (hw : ∀ e, D₂.w (eE e) = D₁.w e) :
    ∃ φ : ↥(ribbonKernel D₁) ≃ₗ[ℤ] ↥(ribbonKernel D₂),
      (∀ (x : ↥(ribbonKernel D₁)) (e : E₁), (φ x : E₂ → ℤ) (eE e) = (x : E₁ → ℤ) e) ∧
      (∀ x y : ↥(ribbonKernel D₁), ribbonGram D₂ (φ x) (φ y) = ribbonGram D₁ x y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_ribbonKernel_linearEquiv_ribbonGram_eq_of_equiv.solution

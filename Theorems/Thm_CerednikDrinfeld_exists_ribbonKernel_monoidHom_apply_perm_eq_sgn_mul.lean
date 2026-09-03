import Definitions.Def_CerednikDrinfeld_Ribbon
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_ribbonKernel_monoidHom_apply_perm_eq_sgn_mul

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.exists_ribbonKernel_monoidHom_apply_perm_eq_sgn_mul
    {E V : Type} [Fintype E] [DecidableEq E] [DecidableEq V] (D : DegeneracyData E V)
    {S : Type} [Group S] (πV : S →* Equiv.Perm V) (πE : S →* Equiv.Perm E) (sgn : S →* ℤˣ)
    (hw : ∀ (σ : S) (e : E), D.w (πE σ e) = D.w e)
    (hsame : ∀ (σ : S) (e : E), sgn σ = 1 → D.a (πE σ e) = πV σ (D.a e) ∧ D.b (πE σ e) = πV σ (D.b e))
    (hswap : ∀ (σ : S) (e : E), sgn σ = -1 → D.a (πE σ e) = πV σ (D.b e) ∧ D.b (πE σ e) = πV σ (D.a e)) :
    ∃ actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)),
      (∀ (σ : S) (x : ↥(ribbonKernel D)) (e : E),
        (actZ σ x : E → ℤ) (πE σ e) = ((sgn σ : ℤˣ) : ℤ) * (x : E → ℤ) e) ∧
      (∀ (σ : S) (x y : ↥(ribbonKernel D)), ribbonGram D (actZ σ x) (actZ σ y) = ribbonGram D x y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_ribbonKernel_monoidHom_apply_perm_eq_sgn_mul.solution

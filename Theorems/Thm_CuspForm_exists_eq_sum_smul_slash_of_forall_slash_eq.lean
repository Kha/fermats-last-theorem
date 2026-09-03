import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq

set_option autoImplicit false

open scoped ModularForm

theorem CuspForm.exists_eq_sum_smul_slash_of_forall_slash_eq
    {M N : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N),
      F ∣[(2 : ℤ)] γ = F) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ⇑h = F := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq.solution

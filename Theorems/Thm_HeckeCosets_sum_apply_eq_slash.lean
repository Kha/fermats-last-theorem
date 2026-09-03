import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_HeckeCosets_sum_apply_eq_slash

set_option autoImplicit false

open scoped ModularForm

theorem HeckeCosets.sum_apply_eq_slash
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 2}
    (hε : CuspForm.HasNebentypus ε F)
    {Ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
    (hΨ : CuspForm.IsAdelicLiftOfGamma1 F Ψ)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (ρ : Fin (p + 1) → GL (Fin 2) ℚ_[p])
    (hρ : ∀ i : Fin (p + 1), ((ρ i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1])
    {h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ}
    (hh : NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), Ψ (h * AdelicDock.padicToAdelic p (ρ i)⁻¹) =
      (((ε (p : ZMod N))⁻¹ • ModularForm.heckeU 2 p ⇑F +
            (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(2 : ℤ)]
          LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by p2m_exact_reverting @_root_.P2MW.S_HeckeCosets_sum_apply_eq_slash.solution

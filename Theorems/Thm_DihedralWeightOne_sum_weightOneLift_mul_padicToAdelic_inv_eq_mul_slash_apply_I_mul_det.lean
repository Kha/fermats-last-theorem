import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
    (hε : CuspForm.HasNebentypus ε F)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (ρ : Fin (p + 1) → GL (Fin 2) ℚ_[p])
    (hρ : ∀ i : Fin (p + 1), ((ρ i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1])
    {h : AdelicGL2 (𝓞 ℚ) ℚ}
    (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * AdelicDock.padicToAdelic p (ρ i)⁻¹) =
      (p : ℂ) *
        ((((ε (p : ZMod N))⁻¹ • ModularForm.heckeU 1 p ⇑F +
              (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(1 : ℤ)]
            LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I *
          (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det.solution

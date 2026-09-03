import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_exists_W_ne_zero

set_option autoImplicit false

open LanglandsTunnell.Converse.DiscreteFamily
open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.DiscreteFamily

theorem solution (u₀ : ℂ) (k₀ : ℕ) :
    ∃ g : GL (Fin 2) ℝ, W u₀ k₀ (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  refine ⟨1, ?_⟩
  rw [Units.val_one]
  have h1 : nsq (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [nsq]
  have hiy : iy (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [iy, h1]
  have hix : ix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by simp [ix, h1]
  have hkap : kap (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp [kap, h1]
  unfold W
  rw [if_pos (by simp), hix, hiy, hkap, h1]
  simp [LanglandsTunnell.Converse.ArchR.psi, prof, detPow]

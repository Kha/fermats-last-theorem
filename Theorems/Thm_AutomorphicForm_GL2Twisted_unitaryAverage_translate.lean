import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_unitaryAverage_translate

set_option autoImplicit false

open AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.unitaryAverage_translate (F : GL (Fin 2) ℂ → ℂ) (hF : Continuous F)
    (k₀ k₁ : GL (Fin 2) ℂ)
    (h₀ : star (k₀ : Matrix (Fin 2) (Fin 2) ℂ) * (k₀ : Matrix (Fin 2) (Fin 2) ℂ) = 1)
    (h₁ : star (k₁ : Matrix (Fin 2) (Fin 2) ℂ) * (k₁ : Matrix (Fin 2) (Fin 2) ℂ) = 1) :
    unitaryAverage (fun k => F (k₀ * k * k₁)) = unitaryAverage F := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_unitaryAverage_translate.solution

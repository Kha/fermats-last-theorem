import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides

set_option autoImplicit false

open AutomorphicForm.GL2Twisted

theorem
AutomorphicForm.GL2Twisted.twistedTransforms_monomialInput_eq_fibreSides
    (i l : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c) (a₁ a₂ r θ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hr : 0 < r) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    twistedSplitTransform (fun g : GL (Fin 2) ℂ => c (invFrobSq g) * ((monomialInput i l g : ℝ) : ℂ)) a₁ a₂ =
        splitFibreSide i l c a₁ a₂ ∧
    twistedEllipticTransform (fun g : GL (Fin 2) ℂ => c (invFrobSq g) * ((monomialInput i l g : ℝ) : ℂ)) r θ =
        ellipticFibreSide i l c r θ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides.solution

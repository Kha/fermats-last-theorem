import Mathlib
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
import P2M.Sol.S_AutomorphicForm_formalBaseChange_a_b_eq_of_under_eq

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped BigOperators NumberField

theorem AutomorphicForm.formalBaseChange_a_b_eq_of_under_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (π : HeckeEigensystem K ℂ) (w w' : HeightOneSpectrum (𝓞 L))
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
    ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) =
      ((formalBaseChange K L π).a w', (formalBaseChange K L π).b w') := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_formalBaseChange_a_b_eq_of_under_eq.solution

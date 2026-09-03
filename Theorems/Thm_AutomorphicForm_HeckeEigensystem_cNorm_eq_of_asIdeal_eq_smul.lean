import Definitions.Def_AutomorphicForm_ArithCuspRealization
import P2M.Util
import P2M.Sol.S_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w'.asIdeal = σ • w.asIdeal) :
    AutomorphicForm.HeckeEigensystem.cNorm w' = AutomorphicForm.HeckeEigensystem.cNorm w := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul.solution

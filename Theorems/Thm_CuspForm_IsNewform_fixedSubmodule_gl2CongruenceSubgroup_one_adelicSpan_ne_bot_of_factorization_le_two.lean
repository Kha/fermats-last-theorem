import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_fixedSubmodule_gl2CongruenceSubgroup_one_adelicSpan_ne_bot_of_factorization_le_two
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix

set_option autoImplicit false
open Polynomial

theorem CuspForm.IsNewform.fixedSubmodule_gl2CongruenceSubgroup_one_adelicSpan_ne_bot_of_factorization_le_two
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime] (hqM : M.factorization q ≤ 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ) :
    LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1)
      (LocalNewvector.AdelicSpan Φ) ≠ ⊥ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_fixedSubmodule_gl2CongruenceSubgroup_one_adelicSpan_ne_bot_of_factorization_le_two.solution

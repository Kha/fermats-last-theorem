import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_of_module_fractionRing_of_isReduced_baseChange
set_option autoImplicit false
universe u v w x
open scoped TensorProduct

theorem Module.Flat.of_module_fractionRing_of_isReduced_baseChange
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (B₁ : Type w) [CommRing B₁] [Algebra R B₁] [Module.Finite R B₁] [Module.Flat R B₁]
    [IsReduced (TensorProduct R K B₁)]
    (M : Type x) [AddCommGroup M] [Module R M] [Module K M] [Module B₁ M]
    [IsScalarTower R K M] [IsScalarTower R B₁ M] [SMulCommClass K B₁ M] :
    Module.Flat B₁ M := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_of_module_fractionRing_of_isReduced_baseChange.solution

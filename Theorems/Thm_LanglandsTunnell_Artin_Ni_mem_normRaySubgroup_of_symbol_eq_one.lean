import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one
attribute [-instance] LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1
attribute [-simp] AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one

set_option autoImplicit false

open NumberField HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.Artin.Ni_mem_normRaySubgroup_of_symbol_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {i : ↥(primeCarriers K 𝔣)}
    (c : ArtinFieldCore K L 𝔣 i)
    (hCSb : SecondInequalityCTM c.E c.N (modulusExt K c.E c.𝔪))
    (hFI : ∀ F : IntermediateField c.E c.N, (Module.finrank c.E F).Prime
      → FirstInequalityCTM c.E F (modulusExt K c.E c.𝔪))
    (x : c.Ip) (hx : c.ωpi x = 1) : c.Ni x ∈ normRaySubgroup K L 𝔣 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Artin_Ni_mem_normRaySubgroup_of_symbol_eq_one.solution

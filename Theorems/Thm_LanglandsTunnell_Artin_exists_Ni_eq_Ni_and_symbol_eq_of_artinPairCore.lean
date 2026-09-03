import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Artin_exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore
attribute [-instance] LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one

set_option autoImplicit false

open NumberField HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.Artin.exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔣 : Ideal (𝓞 K)} {σ : L ≃ₐ[K] L}
    (D : ∀ i : ↥(primeCarriers K 𝔣), ArtinFieldCore K L 𝔣 i)
    (P : ∀ i j : ↥(primeCarriers K 𝔣), ArtinPairCore K L 𝔣 σ (D i) (D j))
    (hdata_ij : ∀ i j, ∀ F : IntermediateField (P i j).E'' (P i j).N'', (Module.finrank (P i j).E'' F).Prime →
      IdeleFirstIneqData (P i j).E'' (P i j).N'' F (modulusExt K (P i j).E'' (P i j).𝔪'')) :
    ∀ i j : ↥(primeCarriers K 𝔣),
      ∃ (b : (D i).Ip) (b' : (D j).Ip), (D i).Ni b = (D j).Ni b' ∧ (D i).ωpi b = σ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Artin_exists_Ni_eq_Ni_and_symbol_eq_of_artinPairCore.solution

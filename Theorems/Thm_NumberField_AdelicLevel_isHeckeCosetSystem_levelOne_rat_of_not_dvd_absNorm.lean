import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SiegelCoordinates
  IsDedekindDomain

theorem NumberField.AdelicLevel.isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm
    (L : Ideal (𝓞 ℚ)) (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ Ideal.absNorm L)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (ϖ : (v.adicCompletion ℚ)ˣ) (hϖ : (ϖ : v.adicCompletion ℚ) = algebraMap ℚ _ (p : ℚ)) :
    HeckeIntegralSeam.IsHeckeCosetSystem
      (levelOne (𝓞 ℚ) ℚ L ⊓ finiteAdelicGL2Subgroup ℚ) (heckeGen (𝓞 ℚ) ℚ v)
      (fun i : Fin (p + 1) =>
        if (i : ℕ) < p then
          AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ
              (upperUnit (1 : ℚ) (-((i : ℕ) : ℚ)) 1 one_ne_zero one_ne_zero)))
            * heckeGenAt (𝓞 ℚ) ℚ v ϖ
        else
          centralScalar (𝓞 ℚ) ℚ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v ϖ))
            * (heckeGenAt (𝓞 ℚ) ℚ v ϖ)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_isHeckeCosetSystem_levelOne_rat_of_not_dvd_absNorm.solution

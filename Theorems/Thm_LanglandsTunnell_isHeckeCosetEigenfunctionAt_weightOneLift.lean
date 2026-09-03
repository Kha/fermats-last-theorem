import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_ModularForm_HeckeOperator
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift
attribute [-instance] HeckeIntegralSeam.finite_padicInt_quotient_span_p Deep.NTSupply.instNormalRayClassSubgroup
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val

set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open IsDedekindDomain AutomorphicForm.SmoothCusp
open scoped ModularForm MatrixGroups

theorem LanglandsTunnell.isHeckeCosetEigenfunctionAt_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ) (hΦ : Φ.level = Ideal.span {(n : 𝓞 ℚ)})
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ModularForm.heckeU 1 (Ideal.absNorm v.asIdeal) f
          + χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) •
              (f ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix (Ideal.absNorm v.asIdeal))
        = Φ.a v • f) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      IsHeckeCosetEigenfunctionAt ℚ ((productionPinsCompact ℚ).U Φ.level)
        ((productionPinsCompact ℚ).gen v) v (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) (Φ.a v) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_isHeckeCosetEigenfunctionAt_weightOneLift.solution

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_resolventSignChar_sylowH
attribute [-instance] LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldC8H_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldC8H LanglandsTunnell.algebra_fixFldSylowH_fixFldC8H LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE
attribute [-instance] LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup
attribute [-simp] AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false
open NumberField IsDedekindDomain LanglandsTunnell

theorem LanglandsTunnell.exists_resolventSignChar_sylowH
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (χ : HeightOneSpectrum (𝓞 ℚ) → ℂ),
      (∀ v ∉ S₀, ∀ (Q : Ideal (𝓞 L)) (σ : L ≃ₐ[ℚ] L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal →
          IsArithFrobAt (𝓞 ℚ) σ Q → (χ v = 1 ↔ σ ∈ detKer e) ∧ (χ v = -1 ↔ σ ∉ detKer e)) ∧
      (∀ v ∉ S₀, χ v * χ v = 1) ∧
      (∀ v ∉ S₀, (χ v = 1 ↔ ∃ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (detKer e))),
          𝔓.under (𝓞 ℚ) = v ∧ (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1)) ∧
      (∀ v ∉ S₀, (χ v = 1 ↔ ∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e))), 𝔓.under (𝓞 ℚ) = v →
          (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 2)) ∧
      (∀ v ∉ S₀, ∀ Q : Ideal (𝓞 L), Q.IsMaximal → Q.under (𝓞 ℚ) = v.asIdeal → Q.inertia (L ≃ₐ[ℚ] L) = ⊥) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_resolventSignChar_sylowH.solution

import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.SmoothCusp HeckeIntegralSeam

theorem AutomorphicForm.exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant
    (F : Type) [Field F] [NumberField F] (N N' : Ideal (𝓞 F)) (hN : N ≠ ⊥) (hN' : N' ≠ ⊥)
    (a : HeightOneSpectrum (𝓞 F) → ℂ) (φ' : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ'U : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F,
      φ' (g * k) = φ' g)
    (S' : Finset (HeightOneSpectrum (𝓞 F)))
    (hφ' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' →
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N' ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v φ' (a v))
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hsys : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₀ →
      ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) reps)
    (t : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ)
    (ht : ∀ h ∈ t, h ∈ finiteAdelicGL2Subgroup F)
    (hU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      ∑ h ∈ t, l h * φ' (g * k * h) = ∑ h ∈ t, l h * φ' (g * h)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v (fun g => ∑ h ∈ t, l h * φ' (g * h)) (a v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_forall_isHeckeCosetEigenfunctionAt_finTranslateSum_of_levelOne_invariant.solution

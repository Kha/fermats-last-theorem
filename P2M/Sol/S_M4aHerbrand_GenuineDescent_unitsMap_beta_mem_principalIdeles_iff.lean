import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import P2M.Util
namespace P2MW.S_M4aHerbrand_GenuineDescent_unitsMap_beta_mem_principalIdeles_iff

set_option autoImplicit false
open NumberField M4aHerbrand M4aHerbrand.GenuineDescent

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (x : (AdeleRing (𝓞 E) E)ˣ) :
    Units.map (genuineBaseChange E F).β.toMonoidHom x ∈ principalIdeles (𝓞 F) F ↔
      x ∈ principalIdeles (𝓞 E) E := by
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  let D := genuineDescentDatum E F
  obtain ⟨hβinj, hfixed, -, -⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm E F D
  have hβu_inj : Function.Injective (Units.map (genuineBaseChange E F).β.toMonoidHom) :=
    fun a b h => Units.ext (hβinj (congrArg Units.val h))

  have hcompat : ∀ e : Eˣ, Units.map (genuineBaseChange E F).β.toMonoidHom
      (Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* AdeleRing (𝓞 E) E) e)
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (Units.map (algebraMap E F : E →* F) e) :=
    fun e => Units.ext ((genuineBaseChange E F).β_compat e)
  constructor
  · rintro ⟨α, hα⟩

    have hfix : ∀ τ : F ≃ₐ[E] F, τ (α : F) = α := by
      intro τ
      have h1 : D.unitsAct τ (Units.map (genuineBaseChange E F).β.toMonoidHom x)
          = Units.map (genuineBaseChange E F).β.toMonoidHom x := (hfixed _).mpr ⟨x, rfl⟩ τ
      rw [← hα] at h1
      have h2 : ((D.unitsAct τ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) α) :
          (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) (τ α) := D.compat τ α
      rw [h1] at h2
      exact (AdeleRing.algebraMap_injective (𝓞 F) F h2).symm
    obtain ⟨e, he⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed (α : F)).mpr hfix)
    have he0 : e ≠ 0 := by rintro rfl; exact α.ne_zero (by rw [← he, map_zero])
    refine ⟨Units.mk0 e he0, hβu_inj ?_⟩
    rw [hcompat, ← hα]
    congr 1
    exact Units.ext he
  · rintro ⟨e, rfl⟩
    exact ⟨_, (hcompat e).symm⟩

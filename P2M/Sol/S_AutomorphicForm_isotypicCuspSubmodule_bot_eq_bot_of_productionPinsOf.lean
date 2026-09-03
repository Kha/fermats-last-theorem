import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
import P2M.Util
namespace P2MW.S_AutomorphicForm_isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf
attribute [-simp] LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

namespace Ws20
namespace LevelBot2

theorem infinite_heightOneSpectrum (F : Type) [Field F] [NumberField F] :
    Infinite (HeightOneSpectrum (𝓞 F)) := by
  classical
  have key : ∀ p : Nat.Primes, ∃ P : HeightOneSpectrum (𝓞 F),
      P.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)} := by
    intro p
    have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp p.2
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 F)).injective_int]; exact bot_le)
    refine ⟨⟨Q, hQmax.isPrime, fun hQ0 => ?_⟩, hQ⟩
    rw [hQ0, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int] at hQ
    exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp hQ.symm)
  choose P hP using key
  haveI : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOf_prime
  refine Infinite.of_injective P fun p q hpq => ?_
  have h := hP p
  rw [hpq, hP q, Ideal.span_singleton_eq_span_singleton] at h
  have h2 := Int.associated_iff_natAbs.mp h
  rw [Int.natAbs_natCast, Int.natAbs_natCast] at h2
  exact Subtype.ext h2.symm

end Ws20.LevelBot2

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ ⊥ S Ψ = ⊥ := by
  classical
  rw [isotypicCuspSubmodule_eq_bot_iff]
  intro φ hφ
  haveI := Ws20.LevelBot2.infinite_heightOneSpectrum F
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset S
  exact absurd (hφ.hecke_eigen v hv)
    (AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup F v φ (Ψ.a v))

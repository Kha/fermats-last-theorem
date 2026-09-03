import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
namespace P2MW.S_LanglandsTunnell_P2_Artin_mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one

set_option autoImplicit false
open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 K), placeOrd K (projFin K z) w = 0) (hadj : IsAdjuster K 𝔣 z 1) :
    z ∈ unitIdeles K 𝔣 := by
  have h1 : z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) 1)⁻¹ = z := by
    rw [map_one, inv_one, mul_one]
  have hval : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (((projFin K z : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1 :=
    fun v => (placeOrd_eq_zero_iff K (projFin K z) v).mp (hz v)
  refine ⟨hval, fun v hv => ?_, fun τ => ?_⟩
  · have h := (hadj.cong v hv).2
    rw [h1] at h
    exact h
  · have h := hadj.sign τ
    rwa [h1] at h

import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
namespace P2MW.S_LanglandsTunnell_Converse_isNicePinned_twistedDatum_iff_of_forall_notMem_a_eq_b_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws23
namespace TINV

open NumberField IsDedekindDomain AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

variable (K : Type) [Field K] [NumberField K]

theorem twistedDatum_congr (X Y : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hXY : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → X.a v = Y.a v ∧ X.b v = Y.b v)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    twistedDatum K X S archR archC μ uR aR uC kC = twistedDatum K Y S archR archC μ uR aR uC kC := by
  unfold twistedDatum
  congr 1
  · funext v
    rw [(hXY v.1 v.2).1, (hXY v.1 v.2).2]
  · funext v
    rw [(hXY v.1 v.2).1, (hXY v.1 v.2).2]

theorem finiteRootNumber_congr (X Y : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hXY : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → X.a v = Y.a v ∧ X.b v = Y.b v)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    finiteRootNumber K X μ S = finiteRootNumber K Y μ S := by
  unfold finiteRootNumber
  refine finprod_congr fun v => ?_
  split_ifs with hv
  · rfl
  · simp only [goodPlaceRootNumber, (hXY v hv).2]

theorem pinnedRootNumber_congr (X Y : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hXY : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → X.a v = Y.a v ∧ X.b v = Y.b v)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    pinnedRootNumber K X μ S archR archC uR aR uC kC = pinnedRootNumber K Y μ S archR archC uR aR uC kC := by
  unfold pinnedRootNumber
  rw [finiteRootNumber_congr K X Y S hXY μ]

end Ws23.TINV

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem solution
    (K : Type) [Field K] [NumberField K]
    (X Y : HeckeEigensystem K ℂ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hXY : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → X.a v = Y.a v ∧ X.b v = Y.b v)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (L Ld : ℂ → ℂ) (N : ℝ) :
    IsNicePinned (twistedDatum K X S archR archC μ uR aR uC kC) L Ld (pinnedRootNumber K X μ S archR archC uR aR uC kC) N ↔
      IsNicePinned (twistedDatum K Y S archR archC μ uR aR uC kC) L Ld (pinnedRootNumber K Y μ S archR archC uR aR uC kC) N := by
  rw [Ws23.TINV.twistedDatum_congr K X Y S hXY archR archC μ uR aR uC kC,
    Ws23.TINV.pinnedRootNumber_congr K X Y S hXY archR archC μ uR aR uC kC]

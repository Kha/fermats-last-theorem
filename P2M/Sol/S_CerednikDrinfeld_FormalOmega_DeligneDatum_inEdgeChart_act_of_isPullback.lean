import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_inEdgeChart_act_of_isPullback

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped Matrix

namespace B24T

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem comap_sup_smul_top {V W : Type} [AddCommGroup V] [AddCommGroup W] [Module B V] [Module B W]
    (Φ : V ≃ₗ[B] W) (S : Submodule B W) (𝔭 : Ideal B) :
    (S ⊔ 𝔭 • ⊤).comap Φ.toLinearMap = S.comap Φ.toLinearMap ⊔ 𝔭 • ⊤ := by
  rw [Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm, Submodule.map_sup,
    Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem edgeNondegAt_act_of_isPullback
    {π : 𝒪} (h : Matrix.GeneralLinearGroup (Fin 2) K) {d d' : DeligneDatum (K := K) π B}
    (hd : DeligneDatum.IsPullback (K := K) (π := π) B h d d')
    {M' M : FullLattice 𝒪 K} (𝔭 : Ideal B) (hd' : d'.EdgeNondegAt π 𝔭 M' M) :
    d.EdgeNondegAt π 𝔭 (FullLattice.act h M') (FullLattice.act h M) := by
  obtain ⟨hle, hπ, h1, h2⟩ := hd'
  refine ⟨latticeMap_mono h hle, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
    rw [← hwv, ← Matrix.mulVec_smul]
    exact mulVec_mem_latticeMap (hπ ⟨w, hw⟩)
  · intro v hv hmem
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap.mp v.2
    have hw' : (w : Fin 2 → K) ∉ M'.1 := by
      intro hw'
      apply hv
      rw [← hwv]
      exact mulVec_mem_latticeMap hw'
    apply h1 ⟨w, hw⟩ hw'
    rw [hd M, ← comap_sup_smul_top, Submodule.mem_comap]
    have key : (actBaseChange B h M).toLinearMap ((1 : B) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥M.1)) = (1 : B) ⊗ₜ[𝒪] v := by
      show (1 : B) ⊗ₜ[𝒪] latticeMapEquiv h M.1 ⟨w, hw⟩ = (1 : B) ⊗ₜ[𝒪] v
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply]
      exact hwv
    rw [key]
    exact hmem
  · intro v' hv' hmem
    obtain ⟨w', hw', hwv'⟩ := mem_latticeMap.mp v'.2
    have hnd : ¬ ∃ u : ↥M.1, ((⟨w', hw'⟩ : ↥M'.1) : Fin 2 → K) = algebraMap 𝒪 K π • (u : Fin 2 → K) := by
      rintro ⟨u, hu⟩
      apply hv'
      refine ⟨⟨(h : Matrix (Fin 2) (Fin 2) K) *ᵥ (u : Fin 2 → K), mulVec_mem_latticeMap u.2⟩, ?_⟩
      show (v' : Fin 2 → K) = algebraMap 𝒪 K π • ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ (u : Fin 2 → K))
      rw [← Matrix.mulVec_smul, ← hwv']
      exact congrArg _ hu
    apply h2 ⟨w', hw'⟩ hnd
    rw [hd M', ← comap_sup_smul_top, Submodule.mem_comap]
    have key : (actBaseChange B h M').toLinearMap ((1 : B) ⊗ₜ[𝒪] (⟨w', hw'⟩ : ↥M'.1)) = (1 : B) ⊗ₜ[𝒪] v' := by
      show (1 : B) ⊗ₜ[𝒪] latticeMapEquiv h M'.1 ⟨w', hw'⟩ = (1 : B) ⊗ₜ[𝒪] v'
      congr 1
      apply Subtype.ext
      rw [coe_latticeMapEquiv_apply]
      exact hwv'
    rw [key]
    exact hmem

end B24T

theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (h : Matrix.GeneralLinearGroup (Fin 2) K) {d d' : DeligneDatum (K := K) π B}
    (hd : DeligneDatum.IsPullback (K := K) (π := π) B h d d')
    {M' M : FullLattice 𝒪 K} (hd' : d'.InEdgeChart π M' M) :
    d.InEdgeChart π (FullLattice.act h M') (FullLattice.act h M) :=
  fun 𝔭 h𝔭 => B24T.edgeNondegAt_act_of_isPullback h hd 𝔭 (hd' 𝔭 h𝔭)

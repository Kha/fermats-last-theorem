import Definitions.Def_CerednikDrinfeld_MumfordGlueLevel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.isPullback_Spec_map_factor_chartERing
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r n : ℕ)
    (q : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})))
    (hq : q.comp (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})) =
      (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r)))
    (q' : (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}) →+* ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)})))
    (hq' : q'.comp (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)})) =
      (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1 + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 (chartERing 𝒪 π r) π) (Nat.le_succ (n + 1)))))))
      (Spec.map (CommRingCat.ofHom q))
      (Spec.map (CommRingCat.ofHom q'))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_isPullback_Spec_map_factor_chartERing.solution

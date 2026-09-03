import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_mem_smoothLocus_of_mem_range_fst_geomGeneric

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.mem_smoothLocus_of_mem_range_fst_geomGeneric
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (x : ↥(X p (ΓM M H) hj))
    (hx : x ∈ Set.range (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).base) :
    x ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_mem_smoothLocus_of_mem_range_fst_geomGeneric.solution

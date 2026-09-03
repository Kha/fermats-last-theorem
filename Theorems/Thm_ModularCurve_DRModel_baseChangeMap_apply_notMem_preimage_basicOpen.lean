import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] (κ : Type) [CommRing κ] [CharP κ p] (toκ : O →+* κ)
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))) :
    (DRModel.baseChangeMap toκ).base y ∉
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen.solution

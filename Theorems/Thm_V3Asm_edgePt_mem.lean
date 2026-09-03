import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSite
import P2M.Util
import P2M.Sol.S_V3Asm_edgePt_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem V3Asm.edgePt_mem (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) :
    ∀ (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n)),
      V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d ∈ ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n d)).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) ∩ ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n (d + 1))).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) := by p2m_exact_reverting @_root_.P2MW.S_V3Asm_edgePt_mem.solution

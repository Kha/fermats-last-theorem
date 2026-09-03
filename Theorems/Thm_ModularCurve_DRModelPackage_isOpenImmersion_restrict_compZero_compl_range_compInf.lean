import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackage_isOpenImmersion_restrict_compZero_compl_range_compInf

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.isOpenImmersion_restrict_compZero_compl_range_compInf
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    :
    IsOpenImmersion
      ((𝔛.compZero κ ⁻¹ᵁ
          (⟨(Set.range (𝔛.compInf κ).base)ᶜ,
            (@Scheme.Hom.isClosedEmbedding _ _ (𝔛.compInf κ) (𝔛.compInf_isClosedImmersion κ)).isClosed_range.isOpen_compl⟩ :
            (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).Opens)).ι ≫ 𝔛.compZero κ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackage_isOpenImmersion_restrict_compZero_compl_range_compInf.solution

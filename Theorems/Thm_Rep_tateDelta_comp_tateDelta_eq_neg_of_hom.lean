import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_tateDelta_comp_tateDelta_eq_neg_of_hom

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.tateDelta_comp_tateDelta_eq_neg_of_hom {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {R₁ R₂ R₃ : ShortComplex (Rep.{u} k G)} (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact)
    (v : R₁ ⟶ R₂) (w : R₂ ⟶ R₃)
    (h₁ : v.τ₁ ≫ w.τ₁ = 0) (h₂ : v.τ₂ ≫ w.τ₂ = 0) (h₃ : v.τ₃ ≫ w.τ₃ = 0)
    (hC₁ : (ShortComplex.mk v.τ₁ w.τ₁ h₁).ShortExact) (hC₂ : (ShortComplex.mk v.τ₂ w.τ₂ h₂).ShortExact)
    (hC₃ : (ShortComplex.mk v.τ₃ w.τ₃ h₃).ShortExact) (n : ℤ) :
    Rep.tateδ hR₃ n ≫ Rep.tateδ hC₁ (n + 1) = -(Rep.tateδ hC₃ n ≫ Rep.tateδ hR₁ (n + 1)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateDelta_comp_tateDelta_eq_neg_of_hom.solution

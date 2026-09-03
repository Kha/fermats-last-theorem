import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_tateMap_tateDelta_add_tateMap_tateDelta_eq_zero

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.tateMap_tateDelta_add_tateMap_tateDelta_eq_zero {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X Y : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (hY : Y.ShortExact)
    (hR : (X.map (MonoidalCategory.tensorRight Y.X₃)).ShortExact)
    (hC : (Y.map (MonoidalCategory.tensorLeft X.X₃)).ShortExact)
    {D : Rep.{u} k G} (φ : X.X₂ ⊗ Y.X₂ ⟶ D) (φ' : X.X₁ ⊗ Y.X₃ ⟶ D) (φ'' : X.X₃ ⊗ Y.X₁ ⟶ D)
    (h' : X.f ▷ Y.X₂ ≫ φ = X.X₁ ◁ Y.g ≫ φ') (h'' : X.X₂ ◁ Y.f ≫ φ = X.g ▷ Y.X₁ ≫ φ'')
    (n : ℤ) (w : (X.X₃ ⊗ Y.X₃).tateCohomology n) :
    (Rep.tateMap φ' (n + 1)).hom ((Rep.tateδ hR n).hom w)
      + (Rep.tateMap φ'' (n + 1)).hom ((Rep.tateδ hC n).hom w) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_tateMap_tateDelta_add_tateMap_tateDelta_eq_zero.solution

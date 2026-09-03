import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    (k : Type u) [Field k] (L : (Spec (CommRingCat.of k)).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of k)).Modules) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hL.exists_trivialization (IsLocalRing.closedPoint k)
  have hrange : Set.range (𝟙 (Spec (CommRingCat.of k)) : Spec (CommRingCat.of k) ⟶ _).base ⊆
      Set.range U.ι.base := by
    rintro y -
    rw [Scheme.Opens.range_ι]
    have : y = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [this]; exact hxU
  let g : Spec (CommRingCat.of k) ⟶ U := IsOpenImmersion.lift U.ι (𝟙 _) hrange
  have hg : g ≫ U.ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackId _).symm.app L ≪≫
    (Scheme.Modules.pullbackCongr hg.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp g U.ι).app L).symm ≪≫
    (Scheme.Modules.pullback g).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso g⟩

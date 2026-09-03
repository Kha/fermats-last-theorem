import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOver_baseChange_baseChange_iso
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] {R'' : Type u} [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    ∃ (u : SchemeHomOver (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))
          (RelativeGroupLaw.baseChangeStr (j ≫ ι) f))
      (v : SchemeHomOver (RelativeGroupLaw.baseChangeStr (j ≫ ι) f)
          (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))),
      u.1 ≫ v.1 = 𝟙 _ ∧ v.1 ≫ u.1 = 𝟙 _ ∧
      u.1 ≫ pullback.fst f (j ≫ ι) = pullback.fst (pullback.snd f ι) j ≫ pullback.fst f ι ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
        (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr j (RelativeGroupLaw.baseChangeStr ι f))),
        NeronModelInfra.schemeHomOverComp (((G.baseChange ι).baseChange j).mul t x y) u =
          (G.baseChange (j ≫ ι)).mul t (NeronModelInfra.schemeHomOverComp x u)
            (NeronModelInfra.schemeHomOverComp y u) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOver_baseChange_baseChange_iso.solution

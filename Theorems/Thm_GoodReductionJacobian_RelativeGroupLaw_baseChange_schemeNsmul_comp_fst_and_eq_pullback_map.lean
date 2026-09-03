import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.baseChange_schemeNsmul_comp_fst_and_eq_pullback_map
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) :
    (G.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ G.schemeNsmul n ∧
    (G.baseChange ι).schemeNsmul n ≫ pullback.snd f ι = pullback.snd f ι ∧
    (G.baseChange ι).schemeNsmul n =
      pullback.map f ι f ι (G.schemeNsmul n) (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, G.schemeNsmul_over]) (by rw [Category.comp_id, Category.id_comp]) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_baseChange_schemeNsmul_comp_fst_and_eq_pullback_map.solution

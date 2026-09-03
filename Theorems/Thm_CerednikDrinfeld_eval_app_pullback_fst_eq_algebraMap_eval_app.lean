import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem CerednikDrinfeld.eval_app_pullback_fst_eq_algebraMap_eval_app
    {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    {𝒳 S : Scheme.{0}} (f : 𝒳 ⟶ S) (sC : Spec (CommRingCat.of C) ⟶ S)
    (p : Spec (CommRingCat.of R) ⟶ 𝒳)
    (q : Spec (CommRingCat.of C) ⟶ Limits.pullback f sC)
    (hq₁ : q ≫ Limits.pullback.fst f sC = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p)
    (hq₂ : q ≫ Limits.pullback.snd f sC = 𝟙 (Spec (CommRingCat.of C)))
    (V : 𝒳.Opens) (hpV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ p ⁻¹ᵁ V)
    (W : (Limits.pullback f sC).Opens) (hWV : W ≤ (Limits.pullback.fst f sC) ⁻¹ᵁ V)
    (hqW : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ q ⁻¹ᵁ W) :
    (∀ s : 𝒳.presheaf.obj (Opposite.op V),
      (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
          (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom
            ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE hWV).op).hom (((Limits.pullback.fst f sC).app V).hom s)))) =
        algebraMap R C ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
          (((Spec (CommRingCat.of R)).presheaf.map (homOfLE hpV).op).hom ((p.app V).hom s)))) ∧
    (∀ c : C,
      (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
          (((Spec (CommRingCat.of C)).presheaf.map (homOfLE hqW).op).hom
            ((q.app W).hom (((Limits.pullback f sC).presheaf.map (homOfLE (hWV.trans le_top : W ≤ ⊤)).op).hom
              ((Limits.pullback.snd f sC).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c))))) = c) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_eval_app_pullback_fst_eq_algebraMap_eval_app.solution

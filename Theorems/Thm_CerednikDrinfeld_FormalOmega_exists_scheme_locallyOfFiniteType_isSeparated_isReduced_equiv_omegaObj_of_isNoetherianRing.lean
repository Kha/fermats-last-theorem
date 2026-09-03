import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing
attribute [-instance] CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra
attribute [-simp] AlgebraicGeometry.Scheme.nilpPoints_map_val CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem CerednikDrinfeld.FormalOmega.exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    :
    ∃ (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (WittVector p k ⧸ pIdeal p (WittVector p k)))) (_ : LocallyOfFiniteType πY)
      (_ : IsSeparated πY) (_ : IsReduced Y)
      (eY : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)), (p : B) = 0 →
        ({x : Spec (CommRingCat.of B) ⟶ Y // x ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)} ≃ OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)),
      ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
        (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
        (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hp : (p : B) = 0) (hp' : (p : B') = 0)
        (g : B →ₐ[ℤ_[p]] B') (hg : (g : B →+* B').comp ψ = ψ')
        (y : {x : Spec (CommRingCat.of B) ⟶ Y // x ≫ πY ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) = Spec.map (CommRingCat.ofHom ψ)}),
        eY B' ψ' hB' hp' ⟨Spec.map (CommRingCat.ofHom (g : B →+* B')) ≫ y.1, by
            rw [Category.assoc, y.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]⟩ =
          DeligneDatum.map (K := ℚ_[p]) (p : ℤ_[p]) g (eY B ψ hB hp y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_exists_scheme_locallyOfFiniteType_isSeparated_isReduced_equiv_omegaObj_of_isNoetherianRing.solution

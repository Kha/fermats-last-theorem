import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing
attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀
attribute [-simp] CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst

set_option autoImplicit false

open CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic TensorProduct

open CategoryTheory AlgebraicGeometry

theorem CerednikDrinfeld.FormalOmega.Omega.exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra ℤ_[p] C] (hC : IsNilpotent (algebraMap ℤ_[p] C p)) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of C))
      (pt : ∀ (S : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S],
        (Omega ℚ_[p] (p : ℤ_[p])).obj S ≃ (Scheme.nilpPoints f).obj S)
      (j : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] →
        (Spec (CommRingCat.of (C ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p)) ⟶ X)),
      (∀ (S S' : Type) [CommRing S] [Algebra C S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] C S]
          [CommRing S'] [Algebra C S'] [Algebra ℤ_[p] S'] [IsScalarTower ℤ_[p] C S']
          (φ : S →ₐ[C] S') (d : (Omega ℚ_[p] (p : ℤ_[p])).obj S),
          pt S' ((Omega ℚ_[p] (p : ℤ_[p])).map (φ.restrictScalars ℤ_[p]) d) = (Scheme.nilpPoints f).map φ (pt S d)) ∧
      (∀ γ, IsOpenImmersion (j γ)) ∧
      (∀ γ, j γ ≫ f = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[ℤ_[p]] chartERing ℤ_[p] (p : ℤ_[p]) p))) ∧
      (∀ x : X, ∃ γ, x ∈ Set.range (j γ).base) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_Omega_exists_scheme_equiv_nilpPoints_and_isOpenImmersion_of_isNoetherianRing.solution

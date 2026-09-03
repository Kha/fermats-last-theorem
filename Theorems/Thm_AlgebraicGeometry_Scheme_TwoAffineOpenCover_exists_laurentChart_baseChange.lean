import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_baseChange
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (Λ : (𝒱.cover c).LaurentChart) :
    ∃ ΛA : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
      (∀ y : (𝒱.cover c).A01,
        ΛA.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) ∧
      (∀ Λ' : ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).LaurentChart,
        (∀ y : (𝒱.cover c).A01,
          Λ'.expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c A).map01 y) = (Λ.expand y).map (algebraMap R A)) →
        Λ' = ΛA) ∧
      (Λ.IsRegular (𝒱.cover c).ρ0 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.IsRegular (𝒱.cover c).ρ1 →
        ΛA.IsRegular ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) ∧
      (Λ.HasParameter (𝒱.cover c).ρ0 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ0) ∧
      (Λ.HasParameter (𝒱.cover c).ρ1 →
        ΛA.HasParameter ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).ρ1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange.solution

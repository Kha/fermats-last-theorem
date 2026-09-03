import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_injective_comp_and_exists_comp_eq_of_isProper

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.IsAdicFrame.injective_comp_and_exists_comp_eq_of_isProper
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀] {π : 𝒪}
    {C : Type} [Field C] [Algebra K₀ C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R)
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of 𝒪)) [IsProper f] :
    Function.Injective (fun p : {p : Spec (CommRingCat.of R) ⟶ X // p ≫ f = Scheme.specOver R} =>
        Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1) ∧
      ∀ cpt : Spec (CommRingCat.of C) ⟶ X, cpt ≫ f = Scheme.specOver C →
        ∃ p : {p : Spec (CommRingCat.of R) ⟶ X // p ≫ f = Scheme.specOver R},
          Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ p.1 = cpt := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_injective_comp_and_exists_comp_eq_of_isProper.solution

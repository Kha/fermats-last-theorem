import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.IsAdicFrame.isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] {π : 𝒪}
    {C : Type} [Field C] [Algebra K₀ C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀] [IsAlgClosed C]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (ϖ : PseudoUniformizer K₀ C) (hF : IsAdicFrame π ϖ R) :
    IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R ∧
      ∃ _ : IsDomain R, ValuationRing R ∧ IsFractionRing R C ∧ IsAlgClosed (FractionRing R) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_isAdicComplete_and_exists_valuationRing_isFractionRing_isAlgClosed.solution

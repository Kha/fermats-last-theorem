import Definitions.Def_CerednikDrinfeld_TwoPlaceTorsionDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching

set_option autoImplicit false

p2m_open "ModularCurve CerednikDrinfeld~ribbon_kernelEquiv"

theorem CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_matching
    {p : ℕ} {E₁ V₁ E₁' V₁' E₂ V₂ E₂' V₂' : Type}
    [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [Fintype E₁'] [Fintype V₁'] [DecidableEq V₁']
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂] [Fintype E₂'] [Fintype V₂'] [DecidableEq V₂']
    {D₁ : DegeneracyData E₁ V₁} {H₁ : HeckeData D₁} {D₁' : DegeneracyData E₁' V₁'} {H₁' : HeckeData D₁'}
    {D₂ : DegeneracyData E₂ V₂} {H₂ : HeckeData D₂} {D₂' : DegeneracyData E₂' V₂'} {H₂' : HeckeData D₂'}
    (M₁ : Matching H₁ H₁') (M₂ : Matching H₂ H₂')
    {A₁ A₂ : ValuationSubring (AlgebraicClosure ℚ)}
    (𝒥 : TwoPlaceTorsionDatum p D₁ H₁ D₂ H₂ A₁ A₂)
    (M : ℕ) (r₁ r₂ : ℕ) [Fact r₁.Prime] [Fact r₂.Prime]
    (h𝒥 : 𝒥.Laws M r₁ r₂) :
    ∃ 𝒥' : TwoPlaceTorsionDatum p D₁' H₁' D₂' H₂' A₁ A₂, 𝒥'.Laws M r₁ r₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_TwoPlaceTorsionDatum_exists_laws_of_matching.solution

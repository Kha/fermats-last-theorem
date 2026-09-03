import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_telescope
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W)
    (M : AlgebraicCurve.SemistableModel A ↥(fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
      (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
      (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
      (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e))
    (D : M.Descent) :
    ∃ (M₁ : AlgebraicCurve.SemistableModel A ↥(fieldBar q M') 𝒞.teleFbar 𝒞.teleChart 𝒞.teleAn 𝒞.teleSrc 𝒞.teleTgt
        𝒞.teleXs 𝒞.teleXt) (D₁ : M₁.Descent), M₁.X = M.X := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope.solution

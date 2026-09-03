import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_partition_of_cover_of_disjoint

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.FullLevel.partition_of_cover_of_disjoint
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (FIg : CuspidalType.ProjLine q → Type) [∀ ℓ, Field (FIg ℓ)] [∀ ℓ, Algebra (ResidueField A) (FIg ℓ)]
    (FSS : ↥W → Type) [∀ s, Field (FSS s)] [∀ s, Algebra (ResidueField A) (FSS s)]
    (CIg : ∀ ℓ, ComponentChart A (fieldBar q M') (FIg ℓ))
    (CSS : ∀ s, ComponentChart A (fieldBar q M') (FSS s))
    (An : CuspidalType.ProjLine q → ↥W → Annulus A (fieldBar q M'))

    (Over : ↥W → Place (AlgebraicClosure ℚ) (fieldBar q M') → Prop)

    (hOrd : ∀ P, (∀ s, ¬ Over s P) → ∃ ℓ, P ∈ (CIg ℓ).dom)

    (hSS : ∀ s P, Over s P → P ∈ (CSS s).dom ∨ ∃ ℓ, P ∈ (An ℓ s).dom)

    (hIgSep : ∀ ℓ ℓ' (P : Place (AlgebraicClosure ℚ) (fieldBar q M')), P ∈ (CIg ℓ).dom → P ∈ (CIg ℓ').dom → ℓ = ℓ')
    (hIgTube : ∀ ℓ, ∀ P ∈ (CIg ℓ).dom, ∀ s, ¬ Over s P)
    (hSSTube : ∀ s, ∀ P ∈ (CSS s).dom, Over s P)

    (hAnDisj : ∀ s ℓ ℓ' P, P ∈ (An ℓ s).dom → P ∈ (An ℓ' s).dom → ℓ = ℓ')
    (hAnTube : ∀ s ℓ, ∀ P ∈ (An ℓ s).dom, Over s P)
    (hAnAvoid : ∀ s ℓ, ∀ P ∈ (An ℓ s).dom, (∀ ℓ', P ∉ (CIg ℓ').dom) ∧ P ∉ (CSS s).dom)

    (hTubeDisj : ∀ s s' P, Over s P → Over s' P → s = s') :
    (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
      (∃ ℓ, P ∈ (CIg ℓ).dom) ∨ (∃ s, P ∈ (CSS s).dom) ∨ (∃ ℓ s, P ∈ (An ℓ s).dom)) ∧
    (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
      (∀ ℓ ℓ', P ∈ (CIg ℓ).dom → P ∈ (CIg ℓ').dom → ℓ = ℓ') ∧
      (∀ s s', P ∈ (CSS s).dom → P ∈ (CSS s').dom → s = s') ∧
      (∀ ℓ s ℓ' s', P ∈ (An ℓ s).dom → P ∈ (An ℓ' s').dom → ℓ = ℓ' ∧ s = s') ∧
      (∀ ℓ s, ¬ (P ∈ (CIg ℓ).dom ∧ P ∈ (CSS s).dom)) ∧
      (∀ ℓ ℓ' s, ¬ (P ∈ (CIg ℓ).dom ∧ P ∈ (An ℓ' s).dom)) ∧
      (∀ s ℓ s', ¬ (P ∈ (CSS s).dom ∧ P ∈ (An ℓ s').dom))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_partition_of_cover_of_disjoint.solution

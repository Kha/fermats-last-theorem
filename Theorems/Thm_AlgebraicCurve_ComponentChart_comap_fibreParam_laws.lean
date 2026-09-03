import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_comap_fibreParam_laws

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.ComponentChart.comap_fibreParam_laws
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar) (P : Place L F) (hPrat : P.IsRational) (T : F)
    (hT : ∃ h : T - algebraMap L F ((σ • P).evalAt T) ∈ C.integers,
      C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap (σ • P)).ord (C.residue ⟨_, h⟩) = 1 ∧
      0 < (σ • P).ord (T - algebraMap L F ((σ • P).evalAt T)) ∧
      ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap (σ • P) → Q ≠ σ • P →
        Q.ord (T - algebraMap L F ((σ • P).evalAt T)) = 0) :
    ∃ h : σ.symm T - algebraMap L F (P.evalAt (σ.symm T)) ∈ (C.comap σ).integers,
      (C.comap σ).residue ⟨_, h⟩ ≠ 0 ∧ ((C.comap σ).placeMap P).ord ((C.comap σ).residue ⟨_, h⟩) = 1 ∧
      0 < P.ord (σ.symm T - algebraMap L F (P.evalAt (σ.symm T))) ∧
      ∀ Q ∈ (C.comap σ).dom, (C.comap σ).placeMap Q = (C.comap σ).placeMap P → Q ≠ P →
        Q.ord (σ.symm T - algebraMap L F (P.evalAt (σ.symm T))) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_comap_fibreParam_laws.solution

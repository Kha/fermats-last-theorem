import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_ord_residue_pos_iff_of_isCentre_of_comap_eq

set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ComponentChart.ord_residue_pos_iff_of_isCentre_of_comap_eq (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)
    (N : Finset (Place (ResidueField A) Fbar))
    (hint : (C.comap σ).integers = C.integers) (hdom : (C.comap σ).dom = C.dom)
    (hrat : ∀ P ∈ C.dom, P.IsRational)
    (O : ValuationSubring F) (hfix : O.comap σ.toAlgHom.toRingHom = O)
    {Q : Place (ResidueField A) Fbar} (hQ : C.IsCentre N O Q)
    (f : F) (hf : f ∈ C.integers) (hσf : σ f ∈ C.integers) (hbd : C.tubeBounded f) :
    0 < Q.ord (C.residue ⟨f, hf⟩) ↔ 0 < Q.ord (C.residue ⟨σ f, hσf⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_pos_iff_of_isCentre_of_comap_eq.solution

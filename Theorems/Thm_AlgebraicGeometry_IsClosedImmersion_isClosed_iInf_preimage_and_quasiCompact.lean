import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.IsClosedImmersion.isClosed_iInf_preimage_and_quasiCompact
    {B E P : Scheme.{u}} (m : E ⟶ P) (hm : IsClosedImmersion m) (πP : P ⟶ B)
    {ι : Type v} [Finite ι] (W : ι → P.Opens)
    (hW : IsClosed ((⨅ j, W j : P.Opens) : Set P)) (hW' : QuasiCompact ((⨅ j, W j).ι ≫ πP)) :
    IsClosed ((⨅ j, m ⁻¹ᵁ (W j) : E.Opens) : Set E) ∧
      QuasiCompact ((⨅ j, m ⁻¹ᵁ (W j)).ι ≫ m ≫ πP) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact.solution

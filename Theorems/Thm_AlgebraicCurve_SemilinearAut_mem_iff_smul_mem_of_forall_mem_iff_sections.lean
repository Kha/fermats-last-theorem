import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_mem_iff_smul_mem_of_forall_mem_iff_sections

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.SemilinearAut.mem_iff_smul_mem_of_forall_mem_iff_sections
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    (g : SemilinearAut L F)
    (hgA : ∀ x : L, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A)
    (S : Subring F) (χ₀ : ↥S →+* ResidueField ↥A)
    (hS : ∀ f : F, f ∈ S ↔ g • f ∈ S)
    (hχ₀ : ∀ f : ↥S, χ₀ ⟨g • (f : F), (hS (f : F)).mp f.2⟩ = χ₀ f)
    (D : Set (Place L F))
    (hD : ∀ P : Place L F, P ∈ D ↔ P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))
    (P : Place L F) :
    P ∈ D ↔ g • P ∈ D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_mem_iff_smul_mem_of_forall_mem_iff_sections.solution

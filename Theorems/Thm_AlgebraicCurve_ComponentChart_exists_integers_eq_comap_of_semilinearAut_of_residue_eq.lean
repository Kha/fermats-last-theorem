import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_exists_integers_eq_comap_of_semilinearAut_of_residue_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.ComponentChart.exists_integers_eq_comap_of_semilinearAut_of_residue_eq
    {L : Type} [Field L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F]
    {Fbar : Type} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (g : SemilinearAut L F)
    (hA : ∀ a : L, a ∈ A ↔ SemilinearAut.baseAut g a ∈ A)
    (hres : ∀ (a : A) (h : SemilinearAut.baseAut g (a : L) ∈ A),
      IsLocalRing.residue A ⟨SemilinearAut.baseAut g (a : L), h⟩ = IsLocalRing.residue A a) :
    ∃ C' : ComponentChart A F Fbar,
      (∀ f : F, f ∈ C'.integers ↔ g • f ∈ C.integers) ∧
      (∀ (f : F) (h' : f ∈ C'.integers) (h : g • f ∈ C.integers), C'.residue ⟨f, h'⟩ = C.residue ⟨g • f, h⟩) ∧
      (∀ P : Place L F, P ∈ C'.dom ↔ g • P ∈ C.dom) ∧
      C'.nodes = C.nodes ∧
      (∀ P : Place L F, C'.placeMap P = C.placeMap (g • P)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_exists_integers_eq_comap_of_semilinearAut_of_residue_eq.solution

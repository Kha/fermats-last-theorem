import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_Descent_exists_finset_mem_subfieldClosure_union_image_algebraMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.Descent.exists_finset_mem_subfieldClosure_union_image_algebraMap
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent) (s : F) :
    ∃ Λ : Finset L, s ∈ Subfield.closure ((D.F₀ : Set F) ∪ (algebraMap L F) '' (↑Λ : Set L)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_Descent_exists_finset_mem_subfieldClosure_union_image_algebraMap.solution

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

theorem AlgebraicCurve.SemistableModel.smul_div_pow_mem_localRing_of_forall_ord_eq
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (k : ℕ) (G : Place L F → ℤ) (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) * G P)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) = G P)
    (c₀ : L) (hc₀ : c₀ ≠ 0)
    (hunit : ∀ i a, M.gen i ∈ U a →
      c₀ • (g / h a ^ k) ∈ (C i).integers ∧ (c₀ • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (a : Fin r) (x : M.X) (hx : x ∈ U a) :
    c₀ • (g / h a ^ k) ∈ SemistableModel.localRing M.X M.ffEquiv x ∧
      (c₀ • (g / h a ^ k))⁻¹ ∈ SemistableModel.localRing M.X M.ffEquiv x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_smul_div_pow_mem_localRing_of_forall_ord_eq.solution

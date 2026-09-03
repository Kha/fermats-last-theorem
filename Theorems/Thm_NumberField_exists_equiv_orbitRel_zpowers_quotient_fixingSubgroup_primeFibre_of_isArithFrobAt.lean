import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_NumberField_exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

theorem NumberField.exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : IntermediateField E L)
    (v : HeightOneSpectrum (𝓞 E)) (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1)
    (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 E) = v)
    (σ : L ≃ₐ[E] L) (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal) :
    ∃ e : MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ((L ≃ₐ[E] L) ⧸ K.fixingSubgroup) ≃ primeFibre E K v,
      ∀ x : (L ≃ₐ[E] L) ⧸ K.fixingSubgroup,
        Nat.card (MulAction.orbit (Subgroup.zpowers σ) x) =
          v.asIdeal.inertiaDeg' ((e (Quotient.mk _ x) : HeightOneSpectrum (𝓞 K)).asIdeal) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt.solution

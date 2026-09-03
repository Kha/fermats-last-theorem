import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

open scoped Classical in

theorem NumberField.sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : Type) [Field K] [NumberField K] [Algebra E K] [Algebra K L] [IsScalarTower E K L]
    (v : HeightOneSpectrum (𝓞 E)) (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1)
    (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 E) = v)
    (σ : L ≃ₐ[E] L) (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal) :
    ((Equiv.Perm.sign (MulAction.toPerm σ :
        Equiv.Perm ((L ≃ₐ[E] L) ⧸ (IsScalarTower.toAlgHom E K L).fieldRange.fixingSubgroup)) : ℤˣ) : ℤ) =
      (-1) ^ (Module.finrank E K + Nat.card (primeFibre E K v)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt.solution

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg
open scoped Pointwise

open scoped Classical in

theorem NumberField.finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : Type) [Field K] [NumberField K] [Algebra E K] [Algebra K L] [IsScalarTower E K L] :
    let H : Subgroup (L ≃ₐ[E] L) := (IsScalarTower.toAlgHom E K L).fieldRange.fixingSubgroup
    let ε : (L ≃ₐ[E] L) →* ℤˣ :=
      (Equiv.Perm.sign : Equiv.Perm ((L ≃ₐ[E] L) ⧸ H) →* ℤˣ).comp (MulAction.toPermHom (L ≃ₐ[E] L) ((L ≃ₐ[E] L) ⧸ H))
    let F : IntermediateField E L := IntermediateField.fixedField ε.ker
    Module.finrank E F ≤ 2 ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)), Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1 →
        ∀ (Q : HeightOneSpectrum (𝓞 L)), Q.under (𝓞 E) = v →
          ∀ (σ : L ≃ₐ[E] L), IsArithFrobAt (𝓞 E) σ Q.asIdeal →
            ∀ w ∈ primeFibre E F v,
              (v.asIdeal.inertiaDeg' w.asIdeal = 1 ↔ ε σ = 1) ∧ (v.asIdeal.inertiaDeg' w.asIdeal = 2 ↔ ε σ = -1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_finrank_fixedField_ker_sign_le_two_and_inertiaDeg_iff_of_isArithFrobAt.solution

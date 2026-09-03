import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_isZero_H1_res_units_of_smul_eq

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.isZero_H1_res_units_of_smul_eq
    (E M : Type) [Field E] [Field M] [Algebra E M] [FiniteDimensional E M]
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M)) :
    ∀ S : Subgroup (M ≃ₐ[E] M),
      CategoryTheory.Limits.IsZero
        (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ)) 1) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_isZero_H1_res_units_of_smul_eq.solution

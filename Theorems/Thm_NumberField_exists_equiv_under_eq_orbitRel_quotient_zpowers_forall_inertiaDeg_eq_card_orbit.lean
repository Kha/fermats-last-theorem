import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_equiv_under_eq_orbitRel_quotient_zpowers_forall_inertiaDeg_eq_card_orbit

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

theorem NumberField.exists_equiv_under_eq_orbitRel_quotient_zpowers_forall_inertiaDeg_eq_card_orbit
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (F : IntermediateField E K)
    (v : HeightOneSpectrum (𝓞 E)) (Q : Ideal (𝓞 K)) [Q.IsMaximal] (hQ : Q.under (𝓞 E) = v.asIdeal)
    (hunr : Q.inertia (K ≃ₐ[E] K) = ⊥)
    (σ : K ≃ₐ[E] K) (hσ : IsArithFrobAt (𝓞 E) σ Q) :
    ∃ e : {u : HeightOneSpectrum (𝓞 F) // u.under (𝓞 E) = v} ≃
        MulAction.orbitRel.Quotient (Subgroup.zpowers σ) ((K ≃ₐ[E] K) ⧸ F.fixingSubgroup),
      ∀ u : {u : HeightOneSpectrum (𝓞 F) // u.under (𝓞 E) = v},
        v.asIdeal.inertiaDeg' (u : HeightOneSpectrum (𝓞 F)).asIdeal =
          Nat.card (MulAction.orbitRel.Quotient.orbit (e u)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_equiv_under_eq_orbitRel_quotient_zpowers_forall_inertiaDeg_eq_card_orbit.solution

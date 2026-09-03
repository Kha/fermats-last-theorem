import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits open AlgebraicGeometry hiding bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected open CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (kbar : Type) [Field kbar]
    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    (ρ : B →+* kbar) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = maximalIdeal B)
    (E₀ : FakeEllipticCurve Λ N kbar) (E' : FakeEllipticCurve Λ N B)
    (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ E' E₀ g')
    (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S) (φ : S →+* B)
    (h h' : E'.A ⟶ E.A)
    (hh : FakeEllipticCurve.IsPullbackVia φ E E' h) (hh' : FakeEllipticCurve.IsPullbackVia φ E E' h')
    (hcomp : g' ≫ h = g' ≫ h') :
    h = h' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_isPullbackVia_of_isPullbackVia_of_comp_eq_comp.solution

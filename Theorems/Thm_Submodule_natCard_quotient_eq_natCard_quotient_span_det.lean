import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_natCard_quotient_eq_natCard_quotient_span_det

set_option autoImplicit false

theorem Submodule.natCard_quotient_eq_natCard_quotient_span_det
    {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (N : Submodule R M) (bN : Module.Basis ι R N) :
    Nat.card (M ⧸ N) = Nat.card (R ⧸ Ideal.span ({b.det (fun i => (bN i : M))} : Set R)) := by p2m_exact_reverting @_root_.P2MW.S_Submodule_natCard_quotient_eq_natCard_quotient_span_det.solution

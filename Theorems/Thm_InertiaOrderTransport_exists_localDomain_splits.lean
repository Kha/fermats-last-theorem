import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.LocalRing.Defs
import P2M.Util
import P2M.Sol.S_InertiaOrderTransport_exists_localDomain_splits

set_option autoImplicit false
open Polynomial

theorem InertiaOrderTransport.exists_localDomain_splits (O' : Type) [CommRing O'] [IsDomain O'] [IsLocalRing O'] :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsLocalRing O'') (j : O' →+* O'')
      (_ : IsLocalHom j) (_ : Function.Injective j),
      ∀ t d : O', ∃ r s : O'', (X ^ 2 - C t * X + C d).map j = (X - C r) * (X - C s) := by p2m_exact_reverting @_root_.P2MW.S_InertiaOrderTransport_exists_localDomain_splits.solution

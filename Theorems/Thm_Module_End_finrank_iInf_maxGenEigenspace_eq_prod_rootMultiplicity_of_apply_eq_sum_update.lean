import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import P2M.Util
import P2M.Sol.S_Module_End_finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update

set_option autoImplicit false

theorem Module.End.finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update
    {F : Type} [Field F] {Q : Type} [Fintype Q] [DecidableEq Q] (ι : Q → Type)
    [∀ q, Fintype (ι q)] [∀ q, DecidableEq (ι q)]
    (C : (q : Q) → Matrix (ι q) (ι q) F)
    (U : Q → Module.End F (((q : Q) → ι q) → F))
    (hU : ∀ (q : Q) (v : ((q : Q) → ι q) → F) (j : (q : Q) → ι q),
      U q v j = ∑ i : ι q, C q (j q) i * v (Function.update j q i))
    (lam : Q → F) :
    Module.finrank F ↥(⨅ q, Module.End.maxGenEigenspace (U q) (lam q)) =
      ∏ q, ((C q).charpoly).rootMultiplicity (lam q) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_eq_prod_rootMultiplicity_of_apply_eq_sum_update.solution

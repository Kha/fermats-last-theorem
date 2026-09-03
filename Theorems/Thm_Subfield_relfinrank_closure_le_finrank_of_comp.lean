import Mathlib
import P2M.Util
import P2M.Sol.S_Subfield_relfinrank_closure_le_finrank_of_comp

set_option autoImplicit false

theorem Subfield.relfinrank_closure_le_finrank_of_comp
    (k : Type) [Field k]
    (E E' : Type) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'] [Module.Finite E E']
    (C Ω : Type) [Field C] [Field Ω] [Algebra k C] [Algebra C Ω] [Algebra k Ω] [IsScalarTower k C Ω]
    (ι : E →+* Ω) (ι' : E' →+* Ω)
    (hι' : ∀ x : E, ι' (algebraMap E E' x) = ι x) :
    Subfield.relfinrank (Subfield.closure (Set.range (algebraMap C Ω) ∪ Set.range ι))
        (Subfield.closure (Set.range (algebraMap C Ω) ∪ Set.range ι')) ≤ Module.finrank E E' := by p2m_exact_reverting @_root_.P2MW.S_Subfield_relfinrank_closure_le_finrank_of_comp.solution

import Mathlib
import P2M.Util
import P2M.Sol.S_LinearIndependent_map_of_finrank_le_relfinrank_closure

set_option autoImplicit false

theorem LinearIndependent.map_of_finrank_le_relfinrank_closure
    (k : Type) [Field k]
    (E E' : Type) [Field E] [Field E'] [Algebra k E] [Algebra k E'] [Algebra E E']
    [IsScalarTower k E E'] [Module.Finite E E']
    (C Ω : Type) [Field C] [Field Ω] [Algebra k C] [Algebra C Ω] [Algebra k Ω] [IsScalarTower k C Ω]
    (ι : E →+* Ω) (ι' : E' →+* Ω)
    (hιk : ∀ z : k, ι (algebraMap k E z) = algebraMap C Ω (algebraMap k C z))
    (hι' : ∀ x : E, ι' (algebraMap E E' x) = ι x)
    (h1 : ∀ t : Finset E, LinearIndependent k (fun x : t => (x : E)) →
      LinearIndependent C (fun x : t => ι (x : E)))
    (h2 : Module.finrank E E' ≤
      Subfield.relfinrank (Subfield.closure (Set.range (algebraMap C Ω) ∪ Set.range ι))
        (Subfield.closure (Set.range (algebraMap C Ω) ∪ Set.range ι'))) :
    ∀ t : Finset E', LinearIndependent k (fun x : t => (x : E')) →
      LinearIndependent C (fun x : t => ι' (x : E')) := by p2m_exact_reverting @_root_.P2MW.S_LinearIndependent_map_of_finrank_le_relfinrank_closure.solution

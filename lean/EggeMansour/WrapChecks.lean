import EggeMansour.Wrap

namespace EggeMansour.Combinatorics

example : List.ofFn (wrap empty) = [1, 0] := by decide
example : List.ofFn (wrap singleton) = [2, 1, 0] := by decide
example : List.ofFn (wrap (Equiv.refl (Fin 2))) = [3, 1, 2, 0] := by decide

#print axioms wrap_zero
#print axioms wrap_last
#print axioms wrap_interior
#print axioms isInvolution_wrap_iff
#print axioms wrap_injective
#print axioms contains_wrap
#print axioms twoCycles_wrap
#print axioms isIndecomposable_wrap

end EggeMansour.Combinatorics

import Forsythe.Matrix.Main

/-!
# Public theorem axiom-footprint regression

The final declarations may use Lean's standard quotient/extensionality/choice
axioms, but must never acquire a project-defined axiom.
-/

/--
info: 'Forsythe.forsythe_s2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Forsythe.forsythe_s2

/--
info: 'Matrix.forsythe_s2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Matrix.forsythe_s2

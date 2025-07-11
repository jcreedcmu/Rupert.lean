import Rupert.AffineRupert
import Rupert.Attr
import Rupert.Basic
import Rupert.Convex
import Rupert.Cube
import Rupert.EuclideanRupert
import Rupert.FinCases
import Rupert.Icosahedron
import Rupert.LinearRupert
import Rupert.MatrixSimps
import Rupert.Quaternion
import Rupert.Equivalences.RupertEquivRupertPrime
import Rupert.Equivalences.RupertEquivRupertSet
import Rupert.Equivalences.AffineRupertEquivRupertSet
import Rupert.Set
import Rupert.SnubCube
import Rupert.Square
import Rupert.Tetrahedron
import Rupert.TriakisTetrahedron

--- main results

/--
info: 'Cube.rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cube.rupert


/--
info: 'Tetrahedron.rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Tetrahedron.rupert


/--
info: 'TriakisTetrahedron.rupert' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TriakisTetrahedron.rupert

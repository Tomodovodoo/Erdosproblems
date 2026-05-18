import Mathlib

/-!
# Raw Pach--Toth Drawing Coordinates

This module records only exact integer data transcribed from the PostScript
drawing and arithmetic facts about that data.  The integer drawing coordinates
are not used here as a metric realization certificate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace Coordinates

/-- A raw integer point from the PostScript drawing. -/
structure DrawPoint where
  x : Int
  y : Int
  deriving DecidableEq, Repr

namespace DrawPoint

/-- Squared Euclidean distance in raw drawing units. -/
def sqDist (p q : DrawPoint) : Int :=
  (p.x - q.x) ^ 2 + (p.y - q.y) ^ 2

theorem sqDist_comm (p q : DrawPoint) : sqDist p q = sqDist q p := by
  dsimp [sqDist]
  ring

end DrawPoint

/-- Squared side lengths for a raw drawing triangle. -/
structure SideSq where
  ab : Int
  ac : Int
  bc : Int
  deriving DecidableEq, Repr

/-- A raw PostScript triangular drawing primitive. -/
structure DrawTriangle where
  a : DrawPoint
  b : DrawPoint
  c : DrawPoint
  deriving DecidableEq, Repr

namespace DrawTriangle

/-- The three squared side lengths in raw drawing units. -/
def sideSq (T : DrawTriangle) : SideSq :=
  { ab := DrawPoint.sqDist T.a T.b
    ac := DrawPoint.sqDist T.a T.c
    bc := DrawPoint.sqDist T.b T.c }

/-- All three squared side lengths equal a proposed scale square. -/
def exactAtScaleSq (T : DrawTriangle) (scaleSq : Int) : Prop :=
  DrawPoint.sqDist T.a T.b = scaleSq /\
    DrawPoint.sqDist T.a T.c = scaleSq /\
    DrawPoint.sqDist T.b T.c = scaleSq

end DrawTriangle

namespace RawFigure2

/-- The natural reading of a unit side as 1000 raw drawing units squared. -/
def scaleSq : Int := 1000 ^ 2

def r1 : DrawPoint := { x := 7225, y := 10800 }

def t0a : DrawPoint := { x := 8091, y := 9300 }
def t0b : DrawPoint := { x := 8091, y := 10300 }
def t0c : DrawPoint := { x := 7225, y := 9800 }
def T0 : DrawTriangle := { a := t0a, b := t0b, c := t0c }

def t1a : DrawPoint := { x := 8091, y := 11300 }
def t1b : DrawPoint := { x := 8091, y := 12300 }
def t1c : DrawPoint := { x := 7225, y := 11800 }
def T1 : DrawTriangle := { a := t1a, b := t1b, c := t1c }

def t2a : DrawPoint := { x := 8760, y := 8557 }
def t2b : DrawPoint := { x := 9069, y := 9509 }
def t2c : DrawPoint := { x := 9738, y := 8766 }
def T2 : DrawTriangle := { a := t2a, b := t2b, c := t2c }

def t3a : DrawPoint := { x := 9581, y := 13184 }
def t3b : DrawPoint := { x := 9091, y := 12312 }
def t3c : DrawPoint := { x := 8581, y := 13172 }
def T3 : DrawTriangle := { a := t3a, b := t3b, c := t3c }

def t4a : DrawPoint := { x := 11170, y := 12502 }
def t4b : DrawPoint := { x := 10179, y := 12382 }
def t4c : DrawPoint := { x := 10574, y := 13301 }
def T4 : DrawTriangle := { a := t4a, b := t4b, c := t4c }

def p1 : DrawPoint := t2c
def q1 : DrawPoint := t4a

theorem p1_eq_t2c : p1 = t2c := rfl
theorem q1_eq_t4a : q1 = t4a := rfl

theorem T0_sideSq :
    T0.sideSq = { ab := scaleSq, ac := 999956, bc := 999956 } := by
  norm_num [DrawTriangle.sideSq, DrawPoint.sqDist, T0, t0a, t0b, t0c, scaleSq]

theorem T0_vertical_side_sqDist : DrawPoint.sqDist t0a t0b = scaleSq := by
  norm_num [DrawPoint.sqDist, t0a, t0b, scaleSq]

theorem T0_first_slanted_side_sqDist : DrawPoint.sqDist t0a t0c = 999956 := by
  norm_num [DrawPoint.sqDist, t0a, t0c]

theorem T0_second_slanted_side_sqDist : DrawPoint.sqDist t0b t0c = 999956 := by
  norm_num [DrawPoint.sqDist, t0b, t0c]

theorem T0_first_slanted_side_not_scaleSq : DrawPoint.sqDist t0a t0c != scaleSq := by
  norm_num [DrawPoint.sqDist, t0a, t0c, scaleSq]

/--
The raw PostScript coordinates for `T0` are not an exact unit equilateral
triangle at scale `1000`: the two slanted sides have squared length `999956`.
-/
theorem raw_T0_not_exact_scale_1000_triangle :
    Not (T0.exactAtScaleSq scaleSq) := by
  norm_num [DrawTriangle.exactAtScaleSq, DrawPoint.sqDist, T0, t0a, t0b, t0c, scaleSq]

/-- One connector side in `U0` has the same raw rounding issue. -/
theorem U0_slanted_side_not_scaleSq : DrawPoint.sqDist r1 t0b != scaleSq := by
  norm_num [DrawPoint.sqDist, r1, t0b, scaleSq]

end RawFigure2

end Coordinates
end PachToth
end ErdosProblems1066

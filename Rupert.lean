import Mathlib


def ThreeSpace := EuclideanSpace ℝ (Fin 3)

notation "ℝ³" => ThreeSpace

def IsRupert (p : Set ℝ³) : Prop := sorry

#check Matrix (Fin 3) (Fin 3) ℚ

def m1 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 2, 3; 4, 5, 6; 7, 8, 9]

#eval m1 * m1

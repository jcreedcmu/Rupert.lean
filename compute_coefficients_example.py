# Example program showing how convex coefficients can be computed.

from sage.numerical.mip import MixedIntegerLinearProgram

points = [
  vector(QQ, [51159677015/62499900187, -88134175589/62499900187]),
  vector(QQ, [-102023148083/62499900187, 97424593/62499900187]),
  vector(QQ, [-115949801/62499900187, -602656159/62499900187]),
  vector(QQ, [50979420869/62499900187, 88639407155/62499900187])
]

q = vector(QQ, [1/1000, -1/1000])

n = len(points)

lp = MixedIntegerLinearProgram(solver='PPL')
lam = lp.new_variable(real=True)

# 1) λ_i ≥ 0
for i in range(n):
    lp.add_constraint(lam[i] >= 0)

# 2) ∑ λ_i = 1
lp.add_constraint(sum(lam[i] for i in range(n)) == 1)

# 3) ∑ λ_i p_i = q
for coord in range(len(q)):
    lp.add_constraint(
        sum(lam[i] * points[i][coord] for i in range(len(lam)))
        == q[coord]
    )

# Dummy objective: minimize 0
lp.set_objective(0)

# Solve and extract
lp.solve()
Lambda = vector(QQ, [lp.get_values(lam[i]) for i in range(n)])

print("Convex coefficients :", Lambda)

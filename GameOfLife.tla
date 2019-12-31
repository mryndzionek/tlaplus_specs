----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers, Sequences

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

Pos == {<<x, y>> : x, y \in 1..N}

TypeOK == grid \in [Pos -> BOOLEAN]

RECURSIVE Sum(_)
Sum(S) == IF S = <<>> THEN 0
                      ELSE Head(S) + Sum(Tail(S))

score(p) == LET sc(a) == LET x == a[1]
                             y == a[2]
                         IN CASE \/ x = 0 \/ y = 0
                                 \/ x > N \/ y > N
                                 \/ ~grid[a] -> 0
                              [] OTHER -> 1
                nbrs == << <<-1, -1>>, <<-1,  0>>, <<-1,  1>>,
                           << 0, -1>>,             << 0,  1>>,
                           << 1, -1>>, << 1,  0>>, << 1,  1>> >>
                points == [n \in DOMAIN nbrs |-> sc(<<p[1] + nbrs[n][1],
                                                      p[2] + nbrs[n][2]>>)]
            IN Sum(points)
                   
Init == grid \in [Pos -> BOOLEAN]
Next == grid' = [p \in Pos |-> IF \/  (grid[p] /\ score(p) \in {2, 3})
                                   \/ (~grid[p] /\ score(p) = 3)
                                THEN TRUE
                                ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================

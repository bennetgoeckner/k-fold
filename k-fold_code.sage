## Copyright (c) 2021, Joseph Doolittle and Bennet Goeckner
## All rights reserved.

## This source code is licensed under the BSD-style license found in the
## LICENSE file in the root directory of this source tree. 

#####################

## Last edited 10/27/2021 by Joseph Doolittle and Bennet Goeckner.
##
## The following complex is Omega from Remark 3.5 in the paper "Resolving Stanley's conjecture on k-fold acyclic complexes."
## This code verifies that Omega is a counterexample to Conjecture 2.4 from Stanley's "A combinatorial decomposition of acyclic simplicial complexes."
## We will first show that the complex is 2-fold acyclic (i.e., link(F) is acyclic for all F such that |F|<2).
## Then we will show, by use of a linear program, that its face poset cannot be fully decomposed into disjoint rank 2 boolean intervals.
##
## Below we give our example and its f-vector. Our example has 20 vertices and 99 facets, and it is pure and three-dimensional.
## More details appear in our paper "Resolving Stanley's conjecture on k-fold acyclic complexes."
##

#####################

Example=SimplicialComplex({ 
        # Gamma
        ('A','B','C','E'),('B','C','E','F'),('B','C','D','F'),('A','B','C','G'),('B','C','G','H'),('B','C','D','H'),('A','B','E','G'),('B','E','F','G'),('B','F','H','G'),
        # Delta1
        ('A','B','C','J1'),('A','B','I1','J1'),('B','C','I1','J1'),('B','C','D','I1'),('C','D','I1','J1'),
        ('A','B','E','K1'),('A','B','I1','K1'),('B','E','I1','K1'),('B','E','F','I1'),('E','F','I1','K1'),
        ('A','B','G','L1'),('A','B','I1','L1'),('B','G','I1','L1'),('B','G','H','I1'),('G','H','I1','L1'),
        ('C','D','F','K1'),('C','D','J1','K1'),('C','F','J1','K1'),('C','E','F','J1'),('E','F','J1','K1'),
        ('C','D','H','L1'),('C','D','J1','L1'),('C','H','J1','L1'),('C','G','H','J1'),('G','H','J1','L1'),
        ('E','F','G','L1'),('E','F','K1','L1'),('F','G','K1','L1'),('F','G','H','K1'),('G','H','K1','L1'),
        # Delta2
        ('A','B','C','J2'),('A','B','I2','J2'),('B','C','I2','J2'),('B','C','D','I2'),('C','D','I2','J2'),
        ('A','B','E','K2'),('A','B','I2','K2'),('B','E','I2','K2'),('B','E','F','I2'),('E','F','I2','K2'),
        ('A','B','G','L2'),('A','B','I2','L2'),('B','G','I2','L2'),('B','G','H','I2'),('G','H','I2','L2'),
        ('C','D','F','K2'),('C','D','J2','K2'),('C','F','J2','K2'),('C','E','F','J2'),('E','F','J2','K2'),
        ('C','D','H','L2'),('C','D','J2','L2'),('C','H','J2','L2'),('C','G','H','J2'),('G','H','J2','L2'),
        ('E','F','G','L2'),('E','F','K2','L2'),('F','G','K2','L2'),('F','G','H','K2'),('G','H','K2','L2'),
        # Delta3
        ('A','B','C','J3'),('A','B','I3','J3'),('B','C','I3','J3'),('B','C','D','I3'),('C','D','I3','J3'),
        ('A','B','E','K3'),('A','B','I3','K3'),('B','E','I3','K3'),('B','E','F','I3'),('E','F','I3','K3'),
        ('A','B','G','L3'),('A','B','I3','L3'),('B','G','I3','L3'),('B','G','H','I3'),('G','H','I3','L3'),
        ('C','D','F','K3'),('C','D','J3','K3'),('C','F','J3','K3'),('C','E','F','J3'),('E','F','J3','K3'),
        ('C','D','H','L3'),('C','D','J3','L3'),('C','H','J3','L3'),('C','G','H','J3'),('G','H','J3','L3'),
        ('E','F','G','L3'),('E','F','K3','L3'),('F','G','K3','L3'),('F','G','H','K3'),('G','H','K3','L3'),
        })
print("The counterexample's f-vector is" , Example.f_vector())


#####################


## The complex itself and the links of all vertices are acyclic; thus the complex is 2-fold acyclic:
##

print("Homology of complex :", Example.homology())
for v in Example.vertices():
    print("Homology of vertex" , v , ":" , Example.link([v]).homology())
	

#####################


## The following linear program tries to decompose a given 3-dimensional complex's face poset into rank 2 boolean intervals (here called ``diamonds'').
##

# Counts the maximum number of diamonds that can appear in a disjoint decomposition. Specific to 3 dimensional complexes.
def DiamondDecomp(Q):

    Diamonds = []

    # Adds a diamond for every possible interval which is topped by a 3-face.
    for f in Q.faces()[3]:
        for e in Subsets(f.set()):
            if len(e)==2:
                D=[]
                for vs in Subsets(f.set().difference(set(e))):
                    D.append(set(e).union(vs))
                Diamonds.append(list(D))

    # Adds a diamond for every possible interval which is topped by a 2-face.
    for t in Q.faces()[2]:
        for v in t.set():
            D=[]
            for vs in Subsets(t.set().difference(set([v]))):
                D.append(set([v]).union(vs))
            Diamonds.append(list(D))

    # Adds a diamond for every possible interval which is topped by a 1-face.
    for e in Q.faces()[1]:
        D=[]
        for vs in Subsets(e.set()):
            D.append(set(vs))
        Diamonds.append(list(D))

    # The LP that shows our example cannot be decomposed into rank 2 boolean intervals.
    p = MixedIntegerLinearProgram(maximization=True)
    v = p.new_variable(binary=True)

    # For each face of the complex, constrains so that the number of diamonds containing that face is less than or equal to 1.
    for sigma in Q.face_iterator():
        p.add_constraint(sum(v[i] * (1 if set(sigma) in Diamonds[i] else 0) for i in range(len(Diamonds))) <= 1)

    # Maximizes the number of the diamonds.
    p.set_objective(sum(v[i] for i in range(len(Diamonds))))
    result=p.solve()
    return result


#####################


## The f-polynomial of our example is f(t) = (1+t)^2*(1+18t+99t^2), so we would need 1+18+99=118 rank 2 boolean intervals to fully decompose the face poset.
## However, we will see below that the largest decomposition the linear program can find contains only 117 rank 2 boolean intervals, therefore the complex is a counterexample to Stanley's conjecture.
##
print("The largest possible decomposition of our example into rank 2 boolean intervals contains only" , DiamondDecomp(Example) , "intervals. It would need 118 intervals to be fully decomposed.")


#####################

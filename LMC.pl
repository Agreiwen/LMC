%Definition opérateur
:- op(20,xfy,?=).

%Les faits

regle(nettoyage).
regle(permutation).
regle(decomposition).
regle(elimination).
regle(fusion).
regle(conlit).
regle(testOcurrence).
fonction(f).
fonction(g).
fonction(h).

%Les regles

regle(E,R) :- R = nettoyage, nettoyage(E);
R = permutation, permutation(E);
R = elimintation, elimination(E);
R = fusion, fusion(E);
R = conflit, conflit(E);
R = decomposition, E = X ?= Y,  functor(X,F,A1), functor(Y,G,A2), F = G, A1 = A2;
R = testOcurrence, testOcurrence(E).

occur_check(V,T) :- V = T, functor(T,F,A), F = T, A = 0;
functor(T,F,A), arg(N, T, V), N < A+1.

%decompose(E) :- r(E,decompose),

%A faire
nettoyage(X ?= Y) :- X = Y.
permutation(X ?= Y) :- X = Y.
elimination(X ?= Y) :- X = Y.
fusion(X ?= Y) :- X = Y.
conflit(X ?= Y) :- X = Y.
testOcurrence(X ?= Y) :- X = Y.
decomposition(X ?= Y) :- X = Y.

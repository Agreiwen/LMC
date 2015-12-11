%Definition opérateur ?=
:- op(20,xfy,?=).

%Definition echo

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).

%Les faits :
poids(clash,5).
poids(check,5).
poids(rename,4).
poids(simplify,4).
poids(orient,3).
poids(decompose,2).
poids(expand,1).

/* Le predicat regle :
Il permet de verifier si une regle en deuxieme parametre
est applicable sur une expression E passee en premier parametre */

regle(E,rename) :- E = _ ?= Y,
	var(Y),
	!.

regle(E,decompose) :- E = X ?= Y,
	compound(X),
	compound(Y),
	functor(Y,NY,AY),
	functor(X,NX,AX),
	NY == NX,
	AY == AX,
	!.

regle(E,simplify) :- E = _ ?= Y,
	atomic(Y),
	!.

regle(E,expand) :- E =X ?= Y,
	compound(Y),
	not(occur_check(X,Y)),
	!.

regle(E,check) :- E = X ?= Y,
	X \== Y,
	occur_check(X,Y),
	!.

regle(E,orient) :- E = X ?= _,
	nonvar(X),
	!.

regle(E,clash) :- E = X ?= Y,
	compound(Y),
	compound(X),
	functor(Y,NY,_),
	functor(X,NX,_),
	NY \== NX,
	!.

regle(E,clash) :- E = X ?= Y,
	compound(Y),
	compound(X),
	functor(Y,_,AY),
	functor(X,_,AX),
	AY \== AX,
	!.

regle(E,clash) :- E = X ?= Y,
	nonvar(X),
	nonvar(Y),
	functor(Y,NY,_),
	functor(X,NX,_),
	NY \== NX,
	!.

regle(E,clash) :- E = X ?= Y,
	nonvar(X),
	nonvar(Y),
	functor(Y,_,AY),
	functor(X,_,AX),
	AY \== AX,
	!.

/* Le predicat occur_check :
Permet de savoir si une variable V appartient à T */

% T n'est pas une fonction (variable ou constante) :
occur_check(V,T) :- V == T,
	!.

% Si T est une fonction :
occur_check(V,T) :- compound(T),
	functor(T,_,A),
	occur_check_arg(V,T,A).

% Si T est une fonction d'arité 1 :
occur_check_arg(V,T,1) :- arg(1,T,Parametre1),
	!,
	occur_check(V,Parametre1).

% Si T est une fonction d'arité >1 :
occur_check_arg(V,T,N) :- arg(N,T,ParamN),
	occur_check(V,ParamN);
	N1 is (N-1),
	occur_check_arg(V,T,N1).

/* Le predicat concatenation :
Il permet de concatener deux listes qu'il reçoit dans les deux
premiers parametres et stock le resultat dans le troiseme */

concat([],X,X).
concat([X|Q],Y,[X|P]) :- concat(Q,Y,P).

substitution([],_,_,[]) :- !.

substitution([A ?= B|P],X,Y,[A2 ?= B2|P2]) :- substitution_terme(A,X,Y,A2),
        substitution_terme(B,X,Y,B2),
        substitution(P,X,Y,P2).

substitution_terme(A,X,Y,Y):-
	A == X,
	not(compound(A)),
	!.

substitution_terme(A,X,_,A):-
	A \== X,
	not(compound(A)),
	!.

substitution_terme(A,X,Y,Q):-functor(A,_,At),
	compound(A),
	substitution_arg(A,X,Y,At,Q),
	!.

substitution_arg(A,X,Y,1,Q):-functor(A,F,At),
        arg(1,A,ValX),
        substitution_terme(ValX,X,Y,Res),
        functor(Q,F,At),
        arg(1,Q,Res),
        !.

substitution_arg(A,X,Y,N,Q):-functor(A,F,At),
        arg(N,A,ValX),
        substitution_terme(ValX,X,Y,Res),
        functor(Q,F,At),
        arg(N,Q,Res),
        N2 is (N-1),
        substitution_arg(A,X,Y,N2,Q),
        !.

substitution2([],_,_,[]):-!.

substitution2([A=B|P],X,T,[A2=B2|P2]):- substitution_terme(A,X,T,A2),
	substitution_terme(B,X,T,B2),
	substitution2(P,X,T,P2).

liste_arg(E,1,L,L2) :- E = X ?= Y,
	arg(1,X,ValX),
        arg(1,Y,ValY),
        L2=[ValX ?= ValY|L],
	!.

liste_arg(E,N,L,L2) :- E = X ?= Y,
	N2 is (N-1),
        arg(N,X,ValX),
        arg(N,Y,ValY),
        liste_arg(X ?= Y,N2,[ValX ?= ValY|L],L2).

/* Le predicat reduit prend en parametre R(la regle), E(equation),
P(reste du systeme d'equation), Q(le resultat de decompose), P2(*/

reduit(R,E,P,Q,P2,Q1):- R == decompose,
	E = X ?= Y,
	Q1 = Q,
	echo(system :[X = Y|P]),
	echo('\n'),
	echo(R :(X = Y)),
	echo('\n'),
	functor(X,_,A),
	liste_arg(X ?= Y,A,[],L),
	concat(L,P,P2),
	!.

reduit(R,E,P,Q,P2,Q1):- R == rename,
	E = X ?= Y,
	echo(system :[X = Y|P]),
	echo('\n'),
	echo(R :(X = Y)),
	echo('\n'),
	substitution(P,X,Y,P2),
	Q1=[X=Y|Q2],
	substitution2(Q,X,Y,Q2),
	!.

reduit(R,E,P,Q,P2,Q1):-R == simplify,
	E = X ?= Y,
	echo(system :[X = Y|P]),
	echo('\n'),
	echo(R :(X = Y)),
	echo('\n'),
	substitution(P,X,Y,P2),
	Q1=[X=Y|Q2],
	substitution2(Q,X,Y,Q2),
	!.

reduit(R,E,P,Q,P2,Q1):-R == expand,
	E = X ?= Y,
	echo(system :[X = Y|P]),
	echo('\n'),
	echo(R :(X = Y)),
	echo('\n'),
	substitution(P,X,Y,P2),
	Q1=[X=Y|Q2],
	substitution2(Q,X,Y,Q2),
	!.

reduit(R,E,P,Q,[X ?= Y|P],Q):- R == orient,
	E = X ?= Y,
	echo(system :[X = Y|P]),
	echo('\n'),
	echo(R :(X = Y)),
	echo('\n'),
	!.

reduit(R,E,P,Q,P,Q):- R == check,
	E = X ?= Y,
	echo(system :[X = Y|P]),
	echo('\n'),
	echo(R :(X = Y)),
	echo('\n'),
	write('\nSystème non unifiable.'),
	autre,
	!.

reduit(R,E,P,Q,P,Q):- R == clash,
	E = X ?= Y,
	echo(system :[X = Y|P]),
	echo('\n'),
	echo(R :(X = Y)),
	echo('\n'),
	write('\nSystème non unifiable.'),
	autre,
	!.

affiche([]):- echo('\n'),
	!.

affiche([X=Y|P]):- echo(X=Y),
	echo('\n'),
	affiche(P).

unifieRes([],Q):- echo('\n'),
	affiche(Q),
	write('Système d\'equation unifiable.'),
	!.

unifieRes([X|P],Q):- regle(X,R1),
	reduit(R1,X,P,Q,P2,Q2),
	unifieRes(P2,Q2).

choix_pondere([],Q,_,_):- echo('\n'),
	affiche(Q),
	write('Système d\'equation unifiable.'),
	!.

choix_pondere(P,Q,E,R):- reglePoidsMax(P,R,E),
	extraitElement(P,E,P2),
	reduit(R,E,P2,Q,P3,Q3),
	choix_pondere(P3,Q3,_,_).

choix_premier([],_,_,_):-!.

choix_premier([E|P],Q,E,R):- regle(E,R),
	reduit(R,E,P,Q,P2,Q2),
	unifieRes(P2,Q2).

reglePoidsMax([X],R,X):-regle(X,R),
	!.

reglePoidsMax([X,Y|P],R,E):- regle(X,R1),
	poids(R1,P1),
	regle(Y,R2),
	poids(R2,P2),
	P1>=P2,
	!,
	reglePoidsMax([X|P],R,E).

reglePoidsMax([X,Y|P],R,E):- regle(X,R1),
	poids(R1,P1),
	regle(Y,R2),
	poids(R2,P2),
	P1=<P2,
	!,
	reglePoidsMax([Y|P],R,E).

extraitElement([],_,[]):- !.

extraitElement([T|R],X,Res):- X == T,
	Res = R,
	!.

extraitElement([T|R],X,Res):- X \== T,
	extraitElement(R,X,Res).

unifie([X|P],Strategie):- Strategie == premier,
	choix_premier([X|P],_,_,_).

unifie(P,Strategie):- Strategie == pondere,
	choix_pondere(P,_,_,_).

trace_unif(P,Strategie):- set_echo,
	unifie(P,Strategie),
	clr_echo,
	!.

unif(P,Strategie):- clr_echo,
	unifie(P,Strategie),
	clr_echo,
	!.

algo(SystEq,Strategie,Trace):- Trace == oui,
	trace_unif(SystEq,Strategie),
	!.

algo(SystEq,Strategie,Trace):- Trace == non,
	unif(SystEq,Strategie),
	!.

projet:- write('\nAlgorithme d\'unification de Martelli-Montanari :\n\n'),
	debut,
	!.

debut:- write('\n\nEcrire le système que vous voulez unifier, par exemple : [f(X,Y) ?= f(Z,h(a)), Z ?= g(X)]\n\n'),
	write('>> Systeme d\'equation à unifier : '),
	read(SystEq),
	write('\n\nQuelle stratégie voulez-vous utiliser ? (Ecrire \'premier\' OU \'pondere\')\n'),
	write('>> Stratégie : '),
	read(Strategie),
	write('\n\nVoulez-vous activer la trace ? (Ecrire \'oui\' OU \'non\')\n'),
	write('>> Trace : '),
	read(Trace),
	write('\n'),
	algo(SystEq,Strategie,Trace),
	autre,
	!.

autre:- write('\n\nVoulez-vous éxécuter l\'algorithme de nouveau ? (Ecrire \'oui\' OU \'non\')\n'),
	write('>> '),
	read(Autre),
	call(verification,Autre),
	!.

verification(Autre):- Autre == oui,
	debut.

verification(Autre):- Autre == non,
	fail,
	!.



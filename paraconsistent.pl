/* -*-prolog-*- */
/* yuki goto, naoyuki nide. 2017.month(4-5)*/

/*
QMPT0 solver for SWI-Prolog

Usage:
	?- qmpt0_refresh.
		Initial the definition of qmpt0_rule/2 and qmpt0_hyp/2.
	?- qmpt0_add_rule(A <= [B1, ..., Bn]).
		Add a QMPT0 clause A <= B1, ..., Bn to the QMPT0 logic program
		expressed by qmpt0_rule/2.
	?- qmpt0_add_fact(A).
		Equivalent to qmpt0_add_rule(A <= []).
	?- qmpt0_solve(A).
		Try to derive A from current QMPT0 logic program expressed by
		qmpt0_rule/2. It may generate alternative solutions.

Predicates internally used:
	qmpt0_rule(A, [B1, ..., Bn])
		Expresses a QMPT0 clause. A fact is expressed as qmpt0_rule(A,
		[]). Asserted by qmpt0_add_rule/1.
	qmpt0_hyp(A, [B1, ..., Bn])
		A QMPT0 clause asserted during the execution of solver
		algorithm. Users do not have to give or modify it manually.

Execution of sample:
	?- qmpt0_test.
	true.
	?- qmpt0_solve(stray(X)).
	X = yuki ;
	X = kuma ;
	false.
*/


/* operator declaration */
:- op(496, fy, -),
   op(497, xfy, <=).

/* dynamic predicate declaration */
:- dynamic qmpt0_rule/2.
:- dynamic qmpt0_hyp/2.

/* interface of our solver engine (meta predicates) */
qmpt0_add_fact(X):-
    asserta(qmpt0_rule(X,[])).

qmpt0_add_rule(X <= Antecedentlist):-
    asserta(qmpt0_rule(X,Antecedentlist)).

qmpt0_refresh :-
    retractall(qmpt0_rule(_,_)),
    retractall(qmpt0_hyp(_,_)).

qmpt0_solve(X):-
    retractall(qmpt0_hyp(_,_)),
    assertz(qmpt0_hyp(X,[X])),
    solve_process(X,[X]).

/* main algorithm of solver */
solve_process(Goal,Subgoalseq) :-
    select(X,Subgoalseq,RestSubgoalseq),
    clause(qmpt0_rule(X,Alist),_),
    append(Alist,RestSubgoalseq,Complexlist),
    list_to_set(Complexlist,NewSubgoalseq),
    (add_qmpt0_hyp(Goal,NewSubgoalseq) -> true ;
	solve_process(Goal,NewSubgoalseq)).

/* sub algorithm for solver; add some clauses as hypotheses to be solved */
add_qmpt0_hyp(_,[]) :- !,true.

add_qmpt0_hyp(Goal,Subgoalseq) :-
    \+clause(qmpt0_hyp(Goal,Subgoalseq),_),
    assertz(qmpt0_hyp(Goal,Subgoalseq)),
    fail.

add_qmpt0_hyp(Goal,Subgoalseq) :-
    select(X,Subgoalseq,Restgoalseq),
    clause(qmpt0_hyp(Goal,Alist),_),
    select(Z,Alist,Rlist),
    (X= -Z; Z= -X),
    append(Restgoalseq,Rlist,Newlist),
    list_to_set_alpha(Newlist,NewSubgoalseq),
    \+clause(qmpt0_hyp(Goal,NewSubgoalseq),_),
    add_qmpt0_hyp(Goal,NewSubgoalseq).

/* similar to list_to_set/2 of SWI-Prolog, but equate and unify the terms
   which are alpha-equivalent */
list_to_set_alpha(L,M):-
    reverse(L,LR),
    list_to_set_alpha_aux(LR,MR),
    reverse(MR,M).
alpha_member(X,[X1|_]) :- X =@= X1, X = X1.
alpha_member(X,[_|L]) :- alpha_member(X,L).

list_to_set_alpha_aux([X|L],M) :-
    alpha_member(X,L), !, list_to_set_alpha_aux(L,M).
list_to_set_alpha_aux([X|L],[X|M]) :- list_to_set_alpha_aux(L,M).
list_to_set_alpha_aux([],[]).

/* test codes */
qmpt0_test:-
    qmpt0_refresh,
    qmpt0_add_rule(stray(X) <= [-in_sight(X),-keep_contact(X,Y)]),
    qmpt0_add_rule(stray(X) <= [keep_contact(X,Y),-present_at(X,Y)]),
    qmpt0_add_fact(in_sight(qbo)),
    qmpt0_add_fact(in_sight(nasu)),
    qmpt0_add_fact(in_sight(megu)),
    qmpt0_add_fact(-in_sight(qbo)),
    qmpt0_add_fact(-in_sight(kuma)),
    qmpt0_add_fact(-in_sight(yuki)),
    qmpt0_add_fact(present_at(qbo,nasubeya)),
    qmpt0_add_fact(present_at(nasu,nasubeya)),
    qmpt0_add_fact(-present_at(yuki,nasubeya)),
    qmpt0_add_fact(keep_contact(megu,nasubeya)),
    qmpt0_add_rule(-present_at(kuma,nasubeya) <= [-in_sight(kuma)]).

qmpt0_test1:-
    qmpt0_refresh,
    qmpt0_add_rule(a(0,Y) <= [b,-c(0,Y)]),
    qmpt0_add_rule(a(Y,1) <= [c(Y,1),d]),
    qmpt0_add_fact(b),
    qmpt0_add_fact(d).

qmpt0_test2:-
    qmpt0_refresh,
    qmpt0_add_rule(a <= [h]),
    qmpt0_add_rule(c <= [-h]),
    qmpt0_add_rule(d <= [c]),
    qmpt0_add_rule(a <= [d, -g]),
    qmpt0_add_rule(a <= [g, -e]),
    qmpt0_add_fact(-e).

qmpt0_test3:-
    qmpt0_refresh,
    qmpt0_add_rule(a <= [b(3)]),
    qmpt0_add_rule(a <= [-b(X), b(f(X))]),
    qmpt0_add_rule(a <= [-b(f(f(f(3))))]).

qmpt0_test4x:-
    qmpt0_refresh,
    qmpt0_add_rule(a <= [b(0,X), c(2,Y)]),
    qmpt0_add_rule(a <= [b(0,X), -c(Y,3)]),
    qmpt0_add_rule(a <= [-b(X,1), c(2,Y)]),
    qmpt0_add_rule(a <= [-b(X,1), -c(Y,3)]).

qmpt0_test4:-
    qmpt0_refresh,
    qmpt0_add_rule(a <= [b, c]),
    qmpt0_add_rule(a <= [b, -c]),
    qmpt0_add_rule(a <= [-b, c]),
    qmpt0_add_rule(a <= [-b, -c]).

qmpt0_test5:-
    qmpt0_refresh,
    qmpt0_add_rule(p <= [q]),
    qmpt0_add_fact(q).

/* test code drivers */
a:-
    qmpt0_test,
    qmpt0_solve(stray(X)), write(X), nl, fail.

b:-
    qmpt0_test1,
    qmpt0_solve(a(X,Y)), write([X,Y]), nl, fail.

c:-
    qmpt0_test2,
    qmpt0_solve(a).

d:-
    qmpt0_test3,
    qmpt0_solve(a).

e:-
    qmpt0_test4,
    qmpt0_solve(a).

f:-
    qmpt0_test4x,
    qmpt0_solve(a).

g:-
    qmpt0_test5,
    qmpt0_solve(p).


% Define all possible sums of two digits as QMPT0 rules:
define_addition_rules :-
    between(0, 9, X),
    between(0, 9, Y),
    Z is X + Y,
    qmpt0_add_rule(sum(X, Y, Z) <= []),
    fail.
define_addition_rules.

ab([X,Y],Z) :-
    setof([X,Y,Z], qmpt0_solve(sum(X, Y, Z)), Solutions),
    member([X,Y,Z], Solutions).

abduce(Args, Result) :-
    setof(Res, ab(Args, Res), UniqueResults),
    member(Result, UniqueResults).
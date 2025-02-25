:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).

% Definitions of the Prolog terms
lit(true).
lit(false).

exactly_one_pos(Vars) :-
        member(lit(true), Vars), 
    select(lit(true), Vars, Rest), 
    set_variable(lit(false), Rest).

set_variable(_, []).
set_variable(Literal, [H|T]):-
    H = Literal,
    set_variable(Literal, T).

min_one_pos([]) :- !.
min_one_pos(Vars) :-
    member(lit(true), Vars),
    maplist(enforce_consistency(Vars), Vars).

enforce_consistency(Vars, lit(true)) :-
    exclude(==(lit(true)), Vars, Rest),
    maplist(=(lit(false)), Rest).
enforce_consistency(_, lit(false)).

% Predicate to normalize logical formulas
normalise(lit(X), lit(X)).
normalise(and(F1, F2), and(NF1, NF2)) :-
    normalise(F1, NF1),
    normalise(F2, NF2).
normalise(or(F1, F2), or(NF1, NF2)) :-
    normalise(F1, NF1),
    normalise(F2, NF2).
normalise(not(not(F)), NF) :-
    normalise(F, NF), !.
normalise(not(F), not(NF)) :-
    normalise(F, NF).
normalise(equivalence(F1, F2), and(or(not(NF1), NF2), or(not(NF2), NF1))) :-
    normalise(F1, NF1),
    normalise(F2, NF2).
normalise(implies(F1, F2), or(not(NF1), NF2)) :-
    normalise(F1, NF1),
    normalise(F2, NF2).
normalise(exactly_one_pos(F1), NF1):-
    exactly_one_pos(F1),
    generate(F1, Result),
    normalise(Result, NF1).
normalise(min_one_pos(F1), NF1):-
    min_one_pos(F1),
    generate(F1, Result),
    normalise(Result, NF1).
    
generate([H|T], H):-
    T = [], !.
generate([H|T], or(H, Result)):-
    generate(T, Result).

% Predicate to convert formula to CNF
to_cnf(Formula, List) :-
    normalise(Formula, NFormula),
    resolve(NFormula, RFormula),
    cnf(RFormula, CNF),
    to_list(CNF, List).


resolve(lit(X), lit(X)).
resolve(not(lit(X)), not(lit(X))).
resolve(not(not(F1)), RF):-
    resolve(F1, RF).

resolve(not(and(F1, F2)), or(RF1, RF2)):-
    resolve(not(F1), RF1),
    resolve(not(F2), RF2).

resolve(not(or(F1, F2)), and(RF1, RF2)):-
    resolve(not(F1), RF1),
    resolve(not(F2), RF2).

resolve(and(F1, F2), and(RF1, RF2)):-
    resolve(F1, RF1),
    resolve(F2, RF2).


resolve(or(F1, F2), or(RF1, RF2)):-
    resolve(F1, RF1),
    resolve(F2, RF2).

%Convert the Resolve Formula to CNF
cnf(lit(X), lit(X)).
cnf(not(lit(X)), not(lit(X))).

cnf(or(F1, and(F2, F3)), CNF):-
    cnf(or(F1, F2), CNF1),
    cnf(or(F1, F3), CNF2), 
    cnf(and(CNF1, CNF2), CNF), !.

cnf(or(and(F1, F2), F3), CNF):- 
    cnf(or(F1, F3), CNF1),
    cnf(or(F2, F3), CNF2), 
    cnf(and(CNF1, CNF2), CNF), !.

cnf(and(F1, F2), and(CNF1, CNF2)):-
    cnf(F1, CNF1),
    cnf(F2, CNF2).

cnf(or(F1, F2), CNF):-
    cnf(F1, CNF1),
    cnf(F2, CNF2),  
    ensure_cnf(or(CNF1, CNF2), CNF).

% Ensure that the result is a valid CNF
ensure_cnf(or(F1, and(F2, F3)), CNF) :-
    cnf(or(F1, and(F2, F3)), CNF), !. 

ensure_cnf(or(and(F1, F2), F3), CNF) :-
    cnf(or(and(F1, F2), F3), CNF), !.

ensure_cnf(or(F1, F2), or(CNF1, CNF2)):-
    cnf(F1, CNF1),
    cnf(F2, CNF2).

% visualization of the list
to_list(lit(X), [[X]]).
to_list(not(lit(X)), [[not(X)]]).

to_list(and(F1, F2), List):-
    to_list(F1, LF1),
    to_list(F2, LF2),
    append(LF1, LF2, List).

to_list(or(F1, F2), [[List|Rest]]):-
    merge(or(F1, F2), [List|Rest]).

merge(lit(X), [X]).
merge(not(lit(X)), [not(X)]).
merge(or(F1, F2), List):-
    merge(F1, NF1),
    merge(F2, NF2),
    append(NF1, NF2, List). 

%Start dpll
remove([], _, []).
remove([H|T], VariableToRemove, [Result|RemoveResult]):-
    remove_literal(H, VariableToRemove, Result),
    remove(T, VariableToRemove, RemoveResult).
    
remove_literal([], _, []).
remove_literal([H|T], VariableToRemove, Result) :- 
    H == VariableToRemove, !, 
    remove_literal(T, VariableToRemove, Result).
remove_literal([H|T], VariableToRemove, [H|ResultT]) :- 
    remove_literal(T, VariableToRemove, ResultT).


contains([], _) :- false. 
contains([H|_], Variable) :- H == Variable, !.
contains([_|T], Variable) :- contains(T, Variable).      

negate(not(X), X):-
    var(X), !.
negate(X, not(X)):-
    var(X), !.

remove_clause([], _, []). 
remove_clause([Sublist|T], VariableToRemove, [Sublist|ResultT]) :-
    \+ contains(Sublist, VariableToRemove), !, 
    remove_clause(T, VariableToRemove, ResultT).
remove_clause([_|T], VariableToRemove, Result) :-
    remove_clause(T, VariableToRemove, Result).

simplify(List, Literal, Result):-
    Literal = true, 
    remove_clause(List, true, FirstResult),
    remove(FirstResult, not(true), Result), !.
simplify(List, not(Literal), Result):-
    not(Literal) = not(false), 
    remove_clause(List, not(false), FirstResult),
    remove(FirstResult, false, Result), !.

solve(CNF):-
    bagof(Literals, dpll(CNF, Literals), _).

dpll([], []).
dpll(CNF, [Literal|S]):-
    select_literal(CNF, Literal),
    simplify(CNF, Literal, SCNF),
    dpll(SCNF, S).

select_literal(CNF, Literal) :-
    member([Literal], CNF), !.
select_literal(ListOfLists, Literal) :-
    append(ListOfLists, List),
    find_first_variable(List, Literal).

find_first_variable([H|T], H) :-
    T = [], !.
find_first_variable([H|_], H) :-
        negate(NH, H),
    var(NH).
find_first_variable([H|_], H) :-
        var(H).
find_first_variable([_|T], Result) :-
    find_first_variable(T, Result).
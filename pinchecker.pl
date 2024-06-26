% -*- coding: iso_8859_1 -*-
% 
% File: pinchecker.pl
% Description: Generate Rust code that violates the Pin contract
%
% Version: 0.3.0
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>

:- module(pinchecker, [
    fn_rpil_reduced/3,
    rpil_reduction/3,
    rpil_inst_reduction/3,
    rpil_term_reduction/3,
    lives_even_after_killing/1,
    ctx_typing/3,
    ctx_liveness/3,
    ctx_borrowing/4,
    ctx_pinning/3
]).

:- use_module(library(lists)).

:- multifile fn_typing/3.
:- multifile fn_rpil/2.
:- multifile impl_trait/2.


%% fn_rpil_reduced(+Func, +Ops, -RpilReduced) is det
%
%  Reduces the RPIL (Rust Pin Intermediate Language) instructions for a given function
%
%  @param Func          The function name
%  @param Ops           List of operands
%  @param RpilReduced   Reduced RPIL instructions of the function
%
fn_rpil_reduced(Func, Ops, RpilReduced) :-
        fn_rpil(Func, Rpil),
        rpil_reduction(Ops, Rpil, RpilReduced).


%% rpil_reduction(+Ops, +Rpil, -RpilReduced) is det
%
%  Reduces a list of RPIL instructions
%
%  @param Ops           List of operands
%  @param Rpil          Original RPIL instructions
%  @param RpilReduced   Reduced RPIL instructions
%
rpil_reduction(Ops, Rpil, RpilReduced) :-
        maplist(rpil_inst_reduction(Ops), Rpil, RpilReduced).


%% rpil_inst_reduction(+Ops, +Inst, -InstReduced) is det
%
%  Reduces a single RPIL instruction
%
%  @param Ops           List of operands
%  @param Inst          Original RPIL instruction
%  @param InstReduced   Reduced RPIL instruction
%
rpil_inst_reduction(Ops, Inst, InstReduced) :-
        Inst =.. [Name|Terms],
        maplist(rpil_term_reduction(Ops), Terms, TermsReduced),
        InstReduced =.. [Name|TermsReduced].


%% rpil_term_reduction(+Ops, +Term, -TermReduced) is det
%
%  Reduces a term in an RPIL instruction
%
%  @param Ops           List of operands
%  @param Term          Original term
%  @param TermReduced   Reduced term
%
rpil_term_reduction(Ops, op(Idx), Var) :-
        !, nth0(Idx, Ops, Var).
rpil_term_reduction(Ops, place(Term, P), place(TermReduced, P)) :-
        rpil_term_reduction(Ops, Term, TermReduced), !.
rpil_term_reduction(Ops, deref(Term), deref(TermReduced)) :-
        rpil_term_reduction(Ops, Term, TermReduced), !.


%% ctx_typing(+Stmts, +Var, -Type) is det
%% ctx_typing(?Stmts, ?Var, ?Type) is multi
%
%  Determines the type of a variable in the context of given statements
%
%  @param Stmts List of statements
%  @param Var   The variable to check
%  @param Type  The type of the variable
%
ctx_typing(Stmts, Var, Type) :-
        ground(Stmts), ground(Var),
        ctx_typing_nondet(Stmts, Var, Type), !.
ctx_typing(Stmts, Var, Type) :-
        !, ctx_typing_nondet(Stmts, Var, Type).


ctx_typing_nondet(Stmts, Var, Type) :-
        length(Stmts, L), Stmts = [Stmt|StmtsR],
        Stmt = funcall(L, Func, Args),
        (   Var = L,
            fn_typing(Func, ArgTypes, Type),
            maplist(alive_var_type(StmtsR), Args, ArgTypes)
        ;   ctx_typing(StmtsR, Var, Type)
        ).


alive_var_type(Stmts, Var, Type) :-
    ctx_liveness(Stmts, Var, alive),
    ctx_typing(Stmts, Var, Type).


%% ctx_liveness(+Stmts, +Var, -Liveness) is det
%% ctx_liveness(?Stmts, ?Var, ?Liveness) is multi
%
%  Determines if a variable is alive in the context of given statements
%
%  @param Stmts         List of statements
%  @param Var           The variable to check
%  @param Liveness      'alive' or 'dead'
%
ctx_liveness(Stmts, Var, Liveness) :-
        ground(Stmts), ground(Var),
        ctx_liveness_nondet(Stmts, Var, Liveness), !.
ctx_liveness(Stmts, Var, Liveness) :-
        !, ctx_liveness_nondet(Stmts, Var, Liveness).


ctx_liveness_nondet(Stmts, Var, Liveness) :-
        length(Stmts, L), Stmts = [Stmt|StmtsR],
        Stmt = funcall(L, Func, Args),
        fn_rpil_reduced(Func, [L|Args], RpilInsts),
        ctx_typing(Stmts, L, _),
        (   Var = L,
            Liveness = alive
        ;   ctx_liveness_partial(StmtsR, RpilInsts, Var, Liveness)
        ).


ctx_liveness_partial(Stmts, [], Var, Liveness) :-
         !, ctx_liveness(Stmts, Var, Liveness).
ctx_liveness_partial(Stmts, Insts, Var, Liveness) :-
        Insts = [Inst|InstsR],
        ctx_liveness_partial(Stmts, InstsR, Var, LivenessR),
        (   LivenessR = dead ->
            Liveness = dead
        ;   Inst = rpil_kill(Var) ->
            (   ctx_typing(Stmts, Var, Type),
                lives_even_after_killing(Type) ->
                Liveness = alive
            ;   Liveness = dead
            )
        ;   LivenessR = alive ->
            Liveness = alive
        ).


%% lives_even_after_killing(+Type) is det
%
%  Checks if a type lives even after being killed
%
%  @param Type  The type to check
%
lives_even_after_killing(mutref_T(_)) :- !.
lives_even_after_killing(T) :- impl_trait(T, copy_Tr).


%% ctx_borrowing(+Stmts, +Lhs, -Rhs, -Kind) is det
%% ctx_borrowing(?Stmts, ?Lhs, ?Rhs, ?Kind) is multi
%
%  Determines borrowing relationships between variables
%
%  @param Stmts List of statements
%  @param Lhs   Left-hand side of the borrowing relationship
%  @param Rhs   Right-hand side of the borrowing relationship
%  @param Kind  Type of borrowing ('shared' or 'mutable')
%
ctx_borrowing(Stmts, Lhs, Rhs, Kind) :-
        ground(Stmts), ground(Lhs),
        ctx_borrowing_nondet(Stmts, Lhs, Rhs, Kind), !.
ctx_borrowing(Stmts, Lhs, Rhs, Kind) :-
        !, ctx_borrowing_nondet(Stmts, Lhs, Rhs, Kind).


ctx_borrowing_nondet(Stmts, Lhs, Rhs, Kind) :-
        length(Stmts, L), Stmts = [Stmt|StmtsR],
        Stmt = funcall(L, Func, Args),
        fn_rpil_reduced(Func, [L|Args], RpilInsts),
        ctx_borrowing_partial(StmtsR, RpilInsts, Lhs, Rhs, Kind),
        (origin(Lhs, VarL) -> ctx_liveness(Stmts, VarL, alive)),
        (origin(Rhs, VarR) -> ctx_liveness(Stmts, VarR, alive)).


ctx_borrowing_partial(Stmts, [], Lhs, Rhs, Kind) :-
         !, ctx_borrowing(Stmts, Lhs, Rhs, Kind).
ctx_borrowing_partial(Stmts, Insts, Lhs, Rhs, Kind) :-
        Insts = [Inst|InstsR],
        (   Inst = rpil_borrow(Lhs, Rhs),
            Kind = shared
        ;   Inst = rpil_borrow_mut(Lhs, Rhs),
            Kind = mutable
        ;   Inst = rpil_bind(PL, PR),
            ctx_borrowing_partial(Stmts, InstsR, Prev, Rhs, Kind),
            replace_origin(Lhs, PL, PR, Prev)
        ;   ctx_borrowing_partial(Stmts, InstsR, Lhs, Rhs, Kind)
        ).


%% ctx_pinning(+Stmts, +Place, -Status) is det
%% ctx_pinning(?Stmts, ?Place, ?Status) is multi
%
%  Determines the pinning status of a place in memory
%
%  @param Stmts         List of statements
%  @param Place         The place to check
%  @param Status        Pinning status ('pinned' or 'moved')
%
ctx_pinning(Stmts, Place, Status) :-
        ground(Stmts), ground(Place),
        ctx_pinning_nondet(Stmts, Place, Status), !.
ctx_pinning(Stmts, Place, Status) :-
        !, ctx_pinning_nondet(Stmts, Place, Status).


ctx_pinning_nondet(Stmts, Place, Status) :-
        length(Stmts, L), Stmts = [Stmt|StmtsR],
        Stmt = funcall(L, Func, Args),
        fn_rpil_reduced(Func, [L|Args], RpilInsts),
        (   Place = L,
            Status = unpinned
        ;   ctx_pinning_partial(StmtsR, RpilInsts, Place, Status)
        ).


ctx_pinning_partial(Stmts, [], Place, Status) :-
        !, ctx_pinning(Stmts, Place, Status).
ctx_pinning_partial(Stmts, Insts, Place, Status) :-
        Insts = [Inst|InstsR],
        ctx_pinning_partial(Stmts, InstsR, Place, StatusR),
        (   StatusR = moved ->
            Status = moved
        ;   StatusR = pinned ->
            (   Inst = rpil_move(ContainingPlace),
                ctx_pinning(Stmts, Place, _),
                contagious_origin(ContainingPlace, Place) ->
                Status = moved
            ;   Status = pinned
            )
        ;   StatusR = unpinned ->
            (   Inst = rpil_pin(deref(Borrower)),
                ctx_borrowing(Stmts, Borrower, Place, _) ->
                Status = pinned
            ;   Status = unpinned
            )
        ).


origin(place(X0, _), X) :-
        nonvar(X0), origin(X0, X).
origin(deref(X0), X) :-
        nonvar(X0), origin(X0, X).
origin(X, X).


contagious_origin(place(X0, _), X) :-
        nonvar(X0), contagious_origin(X0, X).
contagious_origin(X, X).


replace_origin(X0, X0, Y, Y).
replace_origin(place(X0, P), X, Y, place(Y0, P)) :-
        replace_origin(X0, X, Y, Y0).
replace_origin(deref(X0), X, Y, deref(Y0)) :-
        replace_origin(X0, X, Y, Y0).

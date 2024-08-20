% -*- coding: iso_8859_1 -*-
%
% File: pinchecker.pl
% Description: Generate Rust code that violates the Pin Contract
%
% Version: 0.4.0
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>

:- module(pinchecker, [
    fn_rpil_reduced/3,
    rpil_reduction/3,
    rpil_inst_reduction/3,
    rpil_term_reduction/3,
    ctx_typing/3,
    ctx_liveness/3,
    lives_even_after_killing/1,
    ctx_borrowing/4,
    follow_deref/4,
    ctx_pinning/3
]).

:- use_module(library(lists)).

:- multifile fn_typing/3.
:- multifile fn_rpil/2.
:- multifile impl_trait/2.
:- multifile does_not_kill_arguments/1.


%% fn_rpil_reduced(?Fn, ?Ops, ?RpilReduced) is nondet
%
%  Reduces the RPIL (Reference Provenance Intermediate Language) instructions for a given function
%
%  @param Fn            The function name
%  @param Ops           List of operands
%  @param RpilReduced   Reduced RPIL instructions of the function
%
fn_rpil_reduced(Fn, Ops, RpilReduced) :-
        fn_rpil(Fn, Rpil),
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
        maplist(rpil_inst_reduction(Ops), Rpil, RpilReduced0), !,
        RpilReduced = RpilReduced0.


%% rpil_inst_reduction(+Ops, +Inst, -InstReduced) is det
%
%  Reduces a single RPIL instruction
%
%  @param Ops           List of operands
%  @param Inst          Original RPIL instruction
%  @param InstReduced   Reduced RPIL instruction
%
rpil_inst_reduction(Ops, rpil_bind(Term1, Term2), Inst) :-
        rpil_term_reduction(Ops, Term1, TermR1), !,
        rpil_term_reduction(Ops, Term2, TermR2), !,
        Inst = rpil_bind(TermR1, TermR2).
rpil_inst_reduction(Ops, rpil_move(Term), Inst) :-
        rpil_term_reduction(Ops, Term, TermR), !,
        Inst = rpil_move(TermR).
rpil_inst_reduction(Ops, rpil_borrow(Term1, Term2), Inst) :-
        rpil_term_reduction(Ops, Term1, TermR1), !,
        rpil_term_reduction(Ops, Term2, TermR2), !,
        Inst = rpil_borrow(TermR1, TermR2).
rpil_inst_reduction(Ops, rpil_borrow_mut(Term1, Term2), Inst) :-
        rpil_term_reduction(Ops, Term1, TermR1), !,
        rpil_term_reduction(Ops, Term2, TermR2), !,
        Inst = rpil_borrow_mut(TermR1, TermR2).
rpil_inst_reduction(Ops, rpil_deref_move(Term), Inst) :-
        rpil_term_reduction(Ops, Term, TermR), !,
        Inst = rpil_deref_move(TermR).
rpil_inst_reduction(Ops, rpil_deref_pin(Term), Inst) :-
        rpil_term_reduction(Ops, Term, TermR), !,
        Inst = rpil_deref_pin(TermR).


%% rpil_term_reduction(+Ops, +Term, -TermReduced) is det
%
%  Reduces a term in an RPIL instruction
%
%  @param Ops           List of operands
%  @param Term          Original term
%  @param TermReduced   Reduced term
%
rpil_term_reduction(Ops, arg(Idx), Reduced) :-
        nth0(Idx, Ops, Var), !,
        Reduced = variable(Var).
rpil_term_reduction(Ops, place(Term, P), Reduced) :-
        rpil_term_reduction(Ops, Term, TermR), !,
        Reduced = place(TermR, P).
rpil_term_reduction(Ops, place_ext(Term), Reduced) :-
        rpil_term_reduction(Ops, Term, TermR), !,
        Reduced = place_ext(TermR).
rpil_term_reduction(Ops, variant_place(Term, V, P), Reduced) :-
        rpil_term_reduction(Ops, Term, TermR), !,
        Reduced = variant_place(TermR, V, P).
rpil_term_reduction(Ops, deref(Term), Reduced) :-
        rpil_term_reduction(Ops, Term, TermR), !,
        Reduced = deref(TermR).


%% ctx_typing(?Stmts, ?Var, ?Type) is nondet
%
%  Determines the type of a variable in the context of given statements
%
%  @param Stmts List of statements
%  @param Var   The variable to check
%  @param Type  The type of the variable
%
ctx_typing(Stmts, Var, Type) :-
        length(Stmts, L), Stmts = [Stmt | StmtsR],
        Stmt = rs_stmt(L, Fn, Args),
        (   Var = L,
            fn_typing(Fn, ArgTypes, Type),
            maplist(alive_var_type(StmtsR), Args, ArgTypes)
        ;   ctx_typing(StmtsR, Var, Type)
        ).


alive_var_type(Stmts, Var, Type) :-
    ctx_liveness(Stmts, Var, alive),
    ctx_typing(Stmts, Var, Type).


%% ctx_liveness(?Stmts, ?Var, ?Liveness) is nondet
%
%  Determines if a variable is alive in the context of given statements
%
%  @param Stmts         List of statements
%  @param Var           The variable to check
%  @param Liveness      'alive' or 'dead'
%
ctx_liveness(Stmts, Var, Liveness) :-
        length(Stmts, L), Stmts = [Stmt | StmtsR],
        Stmt = rs_stmt(L, Fn, Args),
        ctx_typing(Stmts, L, _Type),
        (   Var = L,
            Liveness = alive
        ;   ctx_liveness(StmtsR, Var, LivenessR),
            (   LivenessR = alive,
                memberchk(Var, Args),
                \+ does_not_kill_arguments(Fn),
                ctx_typing(StmtsR, Var, VarType),
                \+ lives_even_after_killing(VarType) ->
                Liveness = dead
            ;   Liveness = LivenessR
            )
        ).


%% lives_even_after_killing(+Type) is semidet
%
%  Checks if a type lives even after being killed
%
%  @param Type  The type to check
%
lives_even_after_killing(mutref_T(_)) :- !.
lives_even_after_killing(T) :- impl_trait(T, copy_Tr).


%% ctx_borrowing(?Stmts, ?Lhs, ?Rhs, ?Kind) is nondet
%
%  Determines borrowing relationships between variables
%
%  @param Stmts List of statements
%  @param Lhs   Left-hand side of the borrowing relationship
%  @param Rhs   Right-hand side of the borrowing relationship
%  @param Kind  Type of borrowing ('shared' or 'mutable')
%
ctx_borrowing(Stmts, Lhs, Rhs, Kind) :-
        length(Stmts, L), Stmts = [Stmt | StmtsR],
        Stmt = rs_stmt(L, Fn, Args),
        fn_rpil_reduced(Fn, [L | Args], RpilInsts),
        ctx_typing(Stmts, L, _Type),
        ctx_borrowing_partial(StmtsR, RpilInsts, Lhs, Rhs, Kind),
        origin(VarL, Lhs), ctx_liveness(Stmts, VarL, alive),
        origin(VarR, Rhs), ctx_liveness(Stmts, VarR, alive).


ctx_borrowing_partial(Stmts, [], Lhs, Rhs, Kind) :-
         ctx_borrowing(Stmts, Lhs, Rhs, Kind).
ctx_borrowing_partial(Stmts, Insts, Lhs, Rhs, Kind) :-
        Insts = [Inst | InstsR],
        (   Inst = rpil_borrow(PL, PR),
            (   follow_deref(Stmts, Insts, PL, Lhs) ->
                follow_deref(Stmts, Insts, PR, Rhs),
                Kind = shared
            )
        ;   Inst = rpil_borrow_mut(PL, PR),
            (   follow_deref(Stmts, Insts, PL, Lhs) ->
                follow_deref(Stmts, Insts, PR, Rhs),
                Kind = mutable
            )
        ;   Inst = rpil_bind(PL, PR), % TODO: Also apply follow_deref on PL and PR
            ctx_borrowing_partial(Stmts, InstsR, Prev, Rhs, Kind),
            replace_origin(Lhs, PL, PR, Prev)
        ;   ctx_borrowing_partial(Stmts, InstsR, Lhs, Rhs, Kind)
        ).


%% follow_deref(?Stmts, ?Insts, ?Place0, ?Place) is nondet
%
%  Follows dereference chains to find the ultimate referenced place
%
%  @param Stmts         List of statements
%  @param Insts         List of RPIL instructions
%  @param Place0        The initial place to follow
%  @param Place         The place without deref(_)'s
%
follow_deref(_, _, variable(Var), variable(Var)).
follow_deref(Stmts, Insts, place(Op0, P), place(Op, P)) :-
        follow_deref(Stmts, Insts, Op0, Op).
follow_deref(Stmts, Insts, place_ext(Op0), place_ext(Op)) :-
        follow_deref(Stmts, Insts, Op0, Op).
follow_deref(Stmts, Insts, variant_place(Op0, V, P), variant_place(Op, V, P)) :-
        follow_deref(Stmts, Insts, Op0, Op).
follow_deref(Stmts, Insts, deref(Op0), Op) :-
        follow_deref(Stmts, Insts, Op0, Op1),
        ctx_borrowing_partial(Stmts, Insts, Op1, Op, _Kind).


origin(Var, variable(Var)).
origin(Var, place(Op, _)) :- origin(Var, Op).
origin(Var, place_ext(Op)) :- origin(Var, Op).
origin(Var, vairant_place(Op, _, _)) :- origin(Var, Op).
origin(Var, deref(Op)) :- origin(Var, Op).


replace_origin(X0, X0, Y, Y) :- !.
replace_origin(place(X0, P), X, Y, place(Y0, P)) :-
        replace_origin(X0, X, Y, Y0).
replace_origin(place_ext(X0), X, Y, place_ext(Y0)) :-
        replace_origin(X0, X, Y, Y0).
replace_origin(variant_place(X0, V, P), X, Y, variant_place(Y0, V, P)) :-
        replace_origin(X0, X, Y, Y0).
replace_origin(deref(X0), X, Y, deref(Y0)) :-
        replace_origin(X0, X, Y, Y0).


%% ctx_pinning(?Stmts, ?Place, ?Status) is nondet
%
%  Determines the pinning status of a variable place
%
%  @param Stmts         List of statements
%  @param Place         The place to check
%  @param Status        'pinned' or 'moved'
%
ctx_pinning(Stmts, Place, Status) :-
        length(Stmts, L), Stmts = [Stmt | StmtsR],
        Stmt = rs_stmt(L, Fn, Args),
        fn_rpil_reduced(Fn, [L | Args], RpilInsts),
        ctx_typing(Stmts, L, _Type),
        ctx_pinning_partial(StmtsR, RpilInsts, Place, Status).


ctx_pinning_partial(Stmts, [], Place, Status) :-
        ctx_pinning(Stmts, Place, Status).
ctx_pinning_partial(Stmts, Insts, Place, Status) :-
        Insts = [Inst | InstsR],
        (   ctx_pinning_partial(Stmts, InstsR, Place, StatusR) ->
            (   Inst = rpil_deref_move(BrwConPlace),
                ctx_borrowing_partial(Stmts, InstsR, BrwConPlace, ConPlace, _Kind),
                containing_place(ConPlace, Place) ->
                Status = moved
            ;   Inst = rpil_move(ConPlace),
                containing_place(ConPlace, Place) ->
                Status = moved
            ;   Status = StatusR
            )
        ;   Inst = rpil_deref_pin(BrwPlace),
            ctx_borrowing_partial(Stmts, InstsR, BrwPlace, Place, _Kind),
            Status = pinned
        ).


containing_place(variable(Var), variable(Var)).
containing_place(Op, place(Op0, _)) :-
        containing_place(Op, Op0).
containing_place(Op, variant_place(Op0, _, _)) :-
        containing_place(Op, Op0).

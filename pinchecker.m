%---------------------------------------------------------------------------%
%
% File: pinchecker.m
% Version: 0.0.3
% Author: Yuxuan Dai <yxdai@smail.nju.edu.cn>
%
% This module provides an compilable implementation of PinChecker.
%
%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- module pinchecker.
:- interface.

:- import_module io.

%---------------------------------------------------------------------------%

:- pred main(io::di, io::uo) is det.

%---------------------------------------------------------------------------%
%---------------------------------------------------------------------------%

:- implementation.

:- import_module int.
:- import_module list.
:- import_module require.
:- import_module solutions.
:- import_module string.

:- type rs_func
    --->    move_F
    ;       unmovable_new_F.

:- type rs_type
    --->    unmovable_T.

:- type rs_stmt
    --->    rs_stmt(
                line    :: int,
                fn      :: rs_func,
                args    :: list(int)
            )
    ;       rs_stmt_uninit(
                line1   :: int
            ).

:- type rpil_op
    --->    arg(int)
    ;       var(int)
    ;       place(rpil_op, int)
    ;       place_ext(rpil_op)
    ;       variant_place(rpil_op, int, int)
    ;       deref(rpil_op).

:- type rpil_inst
    --->    rpil_bind(rpil_op, rpil_op)
    ;       rpil_move(rpil_op)
    ;       rpil_borrow(rpil_op, rpil_op)
    ;       rpil_borrow_mut(rpil_op, rpil_op)
    ;       rpil_deref_move(rpil_op)
    ;       rpil_deref_pin(rpil_op).

%---------------------------------------------------------------------------%

main(!IO) :-
    StmtsUninit = uninit_stmts(2),
    solutions(
        (pred(Stmts::out) is nondet :-
            ctx_typing(StmtsUninit, Stmts, 2, unmovable_T)
        ),
        Solutions
    ),
    Reprs = list.map(debug_rs_stmts, Solutions),
    Sep = "\n--------------------------------\n",
    Repr = string.join_list(Sep, Reprs),
    io.format("%s\n", [s(Repr)], !IO).

:- pred fn_typing(rs_func, list(rs_type), rs_type).
:- mode fn_typing(in, out, in) is det.
:- mode fn_typing(out, out, in) is multi.

fn_typing(move_F, [T], T).
fn_typing(unmovable_new_F, [], unmovable_T).

:- func fn_rpil(rs_func) = list(rpil_inst).

fn_rpil(move_F) = [
    rpil_bind(arg(0),arg(1)),
    rpil_move(arg(1))].
fn_rpil(unmovable_new_F) = [].

    % Reduce the RPIL (Reference Provenance Intermediate Language)
    % instructions for a given function
    %
:- func fn_rpil_reduced(rs_func, list(int)) = list(rpil_inst).

fn_rpil_reduced(Fn, Ops) = RpilReduced :-
    Rpil = fn_rpil(Fn),
    RpilReduced = rpil_reduction(Ops, Rpil).

    % Reduce a list of RPIL instructions
    %
:- func rpil_reduction(list(int), list(rpil_inst)) = list(rpil_inst).

rpil_reduction(Ops, Rpil) = RpilReduced :-
    RpilReduced = list.map(rpil_inst_reduction(Ops), Rpil).

    % Reduce a single RPIL instruction
    %
:- func rpil_inst_reduction(list(int), rpil_inst) = rpil_inst.

rpil_inst_reduction(Ops, rpil_bind(Term1, Term2)) =
    rpil_bind(TermR1, TermR2) :-
    TermR1 = rpil_term_reduction(Ops, Term1),
    TermR2 = rpil_term_reduction(Ops, Term2).
rpil_inst_reduction(Ops, rpil_move(Term)) =
    rpil_move(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_inst_reduction(Ops, rpil_borrow(Term1, Term2)) =
    rpil_borrow(TermR1, TermR2) :-
    TermR1 = rpil_term_reduction(Ops, Term1),
    TermR2 = rpil_term_reduction(Ops, Term2).
rpil_inst_reduction(Ops, rpil_borrow_mut(Term1, Term2)) =
    rpil_borrow_mut(TermR1, TermR2) :-
    TermR1 = rpil_term_reduction(Ops, Term1),
    TermR2 = rpil_term_reduction(Ops, Term2).
rpil_inst_reduction(Ops, rpil_deref_move(Term)) =
    rpil_deref_move(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_inst_reduction(Ops, rpil_deref_pin(Term)) =
    rpil_deref_pin(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).

    % Reduce a term in an RPIL instruction
    %
:- func rpil_term_reduction(list(int), rpil_op) = rpil_op.

rpil_term_reduction(Ops, arg(Idx)) = TermR :-
    ( list.index0(Ops, Idx, Var) ->
        TermR = var(Var)
    ;
        unexpected($pred, "invalid index")
    ).
rpil_term_reduction(_, var(_)) =
    unexpected($pred, "cannot reduce a reduced RPIL operator").
rpil_term_reduction(Ops, place(Term, P)) =
    place(TermR, P) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_term_reduction(Ops, place_ext(Term)) =
    place_ext(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_term_reduction(Ops, variant_place(Term, V, P)) =
    variant_place(TermR, V, P) :-
    TermR = rpil_term_reduction(Ops, Term).
rpil_term_reduction(Ops, deref(Term)) =
    deref(TermR) :-
    TermR = rpil_term_reduction(Ops, Term).

    % Create a list of uninitialized statements
    %
:- func uninit_stmts(int) = list(rs_stmt).

uninit_stmts(L) = Stmts :-
    ( L > 0 ->
        Stmt = rs_stmt_uninit(L),
        Stmts = [Stmt|uninit_stmts(L - 1)]
    ; L = 0 ->
        Stmts = []
    ;
        unexpected($pred, "invalid length")
    ).

    % Determine the type of a variable in the context of given statements
    %
:- pred ctx_typing(list(rs_stmt), list(rs_stmt), int, rs_type).
:- mode ctx_typing(in, out, in, in) is nondet.

ctx_typing([], _, _, _) :-
    unexpected($pred, "cannot pose typing constraints on empty stataments").
ctx_typing([Stmt_in|StmtsR_in], Stmts_out, Var, Type) :-
    Stmt_in = rs_stmt_uninit(L),
    ( Var = L ->
        fn_typing(Fn, ArgTypes, Type),
        list.map(ctx_typing_findvar(StmtsR_in), ArgTypes, Args),
        Stmt_out = rs_stmt(L, Fn, Args),
        apply_ctx_typing_chain(StmtsR_in, StmtsR_out, Args, ArgTypes),
        Stmts_out = [Stmt_out|StmtsR_out]
    ;
        ctx_typing(StmtsR_in, StmtsR_out, Var, Type),
        Stmts_out = [Stmt_in|StmtsR_out]
    ).
ctx_typing([Stmt_in|StmtsR_in], Stmts_out, Var, Type) :-
    Stmt_in = rs_stmt(L, _Fn, _Args),
    ( Var = L ->
        % `Stmt_in' should produce the same type as `Type'
        Stmts_out = [Stmt_in|StmtsR_in]
    ;
        ctx_typing(StmtsR_in, StmtsR_out, Var, Type),
        Stmts_out = [Stmt_in|StmtsR_out]
    ).

    % Find a variable that could possibly be of a certain type
    %
:- pred ctx_typing_findvar(list(rs_stmt), rs_type, int).
:- mode ctx_typing_findvar(in, in, out) is nondet.

ctx_typing_findvar(Stmts, Type, Var) :-
    Stmts = [Stmt|StmtsR],
    (
        (
            Stmt = rs_stmt(L, Fn, _Args),
            fn_typing(Fn, _ArgTypes, Type)
        ;
            Stmt = rs_stmt_uninit(L)
        ),
        Var = L
    ;
        ctx_typing_findvar(StmtsR, Type, Var)
    ).

    % Apply typing constraints to pairs of variables and types
    %
:- pred apply_ctx_typing_chain(list(rs_stmt), list(rs_stmt), list(int), list(rs_type)).
:- mode apply_ctx_typing_chain(in, out, in, in) is nondet.

apply_ctx_typing_chain(In, Out, [], []) :- 
    Out = In.
apply_ctx_typing_chain(In, Out, [Var|VarsR], [Type|TypesR]) :-
    ctx_typing(In, Mid, Var, Type),
    apply_ctx_typing_chain(Mid, Out, VarsR, TypesR).

%---------------------------------------------------------------------------%
%
% Debug utilities: Convert `rs_*' structures to string representations
%

:- func debug_rs_func(rs_func) = string.

debug_rs_func(move_F) = "move".
debug_rs_func(unmovable_new_F) = "Unmovable::new".

:- func debug_rs_type(rs_type) = string.

debug_rs_type(unmovable_T) = "Unmovable".

:- func debug_rs_stmt(rs_stmt) = string.

debug_rs_stmt(rs_stmt(Line, Fn, Args)) = Repr :-
    FnRepr = debug_rs_func(Fn),
    ArgStrs = list.map(
        (func(Arg) = string.format("v%d", [i(Arg)])),
        Args),
    ArgsRepr = string.join_list(", ", ArgStrs),
    Repr = string.format(
        "let v%d = %s(%s);",
        [i(Line), s(FnRepr), s(ArgsRepr)]).
debug_rs_stmt(rs_stmt_uninit(Line)) =
    string.format("let v%d = ..;", [i(Line)]).

:- func debug_rs_stmts(list(rs_stmt)) = string.

debug_rs_stmts(Stmts) = Repr :-
    RevReprs = list.map(debug_rs_stmt, Stmts),
    Reprs = list.reverse(RevReprs),
    Repr = string.join_list("\n", Reprs).

:- func debug_rpil_op(rpil_op) = string.

debug_rpil_op(arg(N)) =
    string.format("_%d", [i(N)]).
debug_rpil_op(var(N)) =
    string.format("v%d", [i(N)]).
debug_rpil_op(place(Op, N)) =
    string.format("%s.p%d", [s(debug_rpil_op(Op)), i(N)]).
debug_rpil_op(place_ext(Op)) =
    string.format("%s.ext", [s(debug_rpil_op(Op))]).
debug_rpil_op(variant_place(Op, N1, N2)) =
    string.format("%s.v%dp%d", [s(debug_rpil_op(Op)), i(N1), i(N2)]).
debug_rpil_op(deref(Op)) =
    string.format("(%s)*", [s(debug_rpil_op(Op))]).

:- func debug_rpil_inst(rpil_inst) = string.

debug_rpil_inst(rpil_bind(Op1, Op2)) =
    string.format(
        "BIND %s, %s",
        [s(debug_rpil_op(Op1)), s(debug_rpil_op(Op2))]).
debug_rpil_inst(rpil_move(Op)) =
    string.format("MOVE %s", [s(debug_rpil_op(Op))]).
debug_rpil_inst(rpil_borrow(Op1, Op2)) =
    string.format(
        "BORROW %s, %s",
        [s(debug_rpil_op(Op1)), s(debug_rpil_op(Op2))]).
debug_rpil_inst(rpil_borrow_mut(Op1, Op2)) =
    string.format(
        "BORROW-MUT %s, %s",
        [s(debug_rpil_op(Op1)), s(debug_rpil_op(Op2))]).
debug_rpil_inst(rpil_deref_move(Op)) =
    string.format("DEREF-MOVE %s", [s(debug_rpil_op(Op))]).
debug_rpil_inst(rpil_deref_pin(Op)) =
    string.format("DEREF-PIN %s", [s(debug_rpil_op(Op))]).

:- func debug_rpil_insts(list(rpil_inst)) = string.

debug_rpil_insts(Insts) = Repr :-
    Reprs = list.map(debug_rpil_inst, Insts),
    Repr = string.join_list("\n", Reprs).

%---------------------------------------------------------------------------%
:- end_module pinchecker.
%---------------------------------------------------------------------------%

%---------------------------------------------------------------------------%
%
% File: pinchecker.m
% Version: 0.0.7
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
    ;       borrow_F
    ;       borrow_mut_F
    ;       store_two_new_F
    ;       unmovable_new_F.

:- type rs_type
    --->    ref_T(rs_type)
    ;       mutref_T(rs_type)
    ;       store_two_T(rs_type, rs_type)
    ;       unmovable_T.

:- type rs_trait
    --->    copy_Tr
    ;       deref_Tr(rs_type)
    ;       derefmut_Tr(rs_type).

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

:- type var_liveness
    --->    alive
    ;       dead.

:- type borrow_kind
    --->    shared
    ;       mutable.

%---------------------------------------------------------------------------%

main(!IO) :-
    StmtsUninit = uninit_stmts(4),
    solutions(
        (pred(Stmts::out) is nondet :-
            Type = store_two_T(unmovable_T, ref_T(unmovable_T)),
            ctx_typing(StmtsUninit, Stmts, 4, Type),
            ctx_borrowing_check(Stmts, var(2), var(1), shared)
        ),
        Solutions
    ),
    Reprs = list.map(debug_rs_stmts, Solutions),
    Sep = "\n--------------------------------\n",
    Repr = string.join_list(Sep, Reprs),
    io.format("%s\n", [s(Repr)], !IO).

:- pred fn_typing(rs_func, list(rs_type), rs_type).
:- mode fn_typing(in, in, out) is semidet.
:- mode fn_typing(out, out, in) is multi.

fn_typing(move_F, [T], T).
fn_typing(borrow_F, [T], ref_T(T)).
fn_typing(borrow_mut_F, [T], mutref_T(T)).
fn_typing(store_two_new_F, [T1, T2], store_two_T(T1, T2)).
fn_typing(unmovable_new_F, [], unmovable_T).

:- func fn_rpil(rs_func) = list(rpil_inst).

fn_rpil(move_F) =
    [ rpil_bind(arg(0), arg(1))
    , rpil_move(arg(1))
    ].
fn_rpil(borrow_F) =
    [ rpil_borrow(arg(0), arg(1))
    ].
fn_rpil(borrow_mut_F) =
    [ rpil_borrow_mut(arg(0), arg(1))
    ].
fn_rpil(store_two_new_F) =
    [ rpil_bind(place(arg(0),1), arg(1))
    , rpil_bind(place(arg(0),2), arg(2))
    , rpil_move(arg(1))
    , rpil_move(arg(2))
    ].
fn_rpil(unmovable_new_F) =
    [ ].

:- pred impl_trait(rs_type, rs_trait).
:- mode impl_trait(in, in) is semidet.

impl_trait(ref_T(_), copy_Tr).
impl_trait(ref_T(T), deref_Tr(T)).
impl_trait(mutref_T(T), derefmut_Tr(T)).

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
        Stmts = [Stmt | uninit_stmts(L - 1)]
    ; L = 0 ->
        Stmts = []
    ;
        unexpected($pred, "invalid length")
    ).

    % Checks if a variable has a specific type
    %
    % This can also be used to get the type of a specific variable
    %
:- pred ctx_typing_check(list(rs_stmt), int, rs_type).
:- mode ctx_typing_check(in, in, out) is semidet.

ctx_typing_check([Stmt | StmtsR], Var, Type) :-
    Stmt = rs_stmt(L, Fn, Args),
    ( Var = L ->
        list.map(ctx_typing_check(StmtsR), Args, ArgTypes),
        fn_typing(Fn, ArgTypes, Type)
    ;
        ctx_typing_check(StmtsR, Var, Type)
    ).
ctx_typing_check([Stmt | StmtsR], Var, Type) :-
    Stmt = rs_stmt_uninit(L),
    ( Var = L ->
        false
    ;
        ctx_typing_check(StmtsR, Var, Type)
    ).

    % Generate statements by applying typing constraints
    %
:- pred ctx_typing(list(rs_stmt), list(rs_stmt), int, rs_type).
:- mode ctx_typing(in, out, in, in) is nondet.

ctx_typing(Stmts_in, Stmts_out, Var, Type) :-
    Stmts_in = [Stmt_in | StmtsR_in],
    Stmt_in = rs_stmt_uninit(L),
    ( Var = L ->
        fn_typing(Fn, ArgTypes, Type),
        list.map(ctx_typing_findvar(StmtsR_in), ArgTypes, Args),
        Stmt_out = rs_stmt(L, Fn, Args),
        apply_ctx_typing_chain(StmtsR_in, StmtsR_out, Args, ArgTypes),
        list.all_true(
            (pred(Arg::in) is semidet :-
                ctx_liveness_check(StmtsR_out, Arg, alive)
            ),
            Args
        ),
        Stmts_out = [Stmt_out | StmtsR_out]
    ;
        ctx_typing(StmtsR_in, StmtsR_out, Var, Type),
        Stmts_out = [Stmt_in | StmtsR_out]
    ).
ctx_typing(Stmts_in, Stmts_out, Var, Type) :-
    Stmts_in = [Stmt_in | StmtsR_in],
    Stmt_in = rs_stmt(L, _Fn, _Args),
    ( Var = L ->
        ctx_typing_check(Stmts_in, Var, Type),
        Stmts_out = [Stmt_in | StmtsR_in]
    ;
        ctx_typing(StmtsR_in, StmtsR_out, Var, Type),
        Stmts_out = [Stmt_in | StmtsR_out]
    ).

    % Find a variable that could possibly be of a certain type
    %
:- pred ctx_typing_findvar(list(rs_stmt), rs_type, int).
:- mode ctx_typing_findvar(in, in, out) is nondet.

ctx_typing_findvar(Stmts, Type, Var) :-
    Stmts = [Stmt | StmtsR],
    (
        (
            Stmt = rs_stmt(L, Fn, Args),
            fn_typing(Fn, ArgTypes, Type),
            list.map(ctx_typing_check(StmtsR), Args, ArgTypes)
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
apply_ctx_typing_chain(In, Out, [Var | VarsR], [Type | TypesR]) :-
    ctx_typing(In, Mid, Var, Type),
    apply_ctx_typing_chain(Mid, Out, VarsR, TypesR).

    % Check the liveness of a variable
    %
    % This can also be used to get the liveness of a specific variable
    %
:- pred ctx_liveness_check(list(rs_stmt), int, var_liveness).
:- mode ctx_liveness_check(in, in, out) is semidet.

ctx_liveness_check([Stmt | _], _, Liveness) :-
    Stmt = rs_stmt_uninit(_L),
    Liveness = alive.
ctx_liveness_check([Stmt | StmtsR], Var, Liveness) :-
    Stmt = rs_stmt(L, Fn, Args),
    ( Var = L ->
        Liveness = alive
    ; list.member(Var, Args) ->
        ctx_liveness_check(StmtsR, Var, alive),
        ( Fn = borrow_F ->
            Liveness = alive
        ; Fn = borrow_mut_F ->
            Liveness = alive
        ; ctx_typing_check(StmtsR, Var, VarType),
          lives_even_after_killing(VarType) ->
            Liveness = alive
        ;
            Liveness = dead
        )
    ;
        ctx_liveness_check(StmtsR, Var, Liveness)
    ).

:- pred lives_even_after_killing(rs_type).
:- mode lives_even_after_killing(in) is semidet.

lives_even_after_killing(mutref_T(_)).
lives_even_after_killing(Type) :-
    impl_trait(Type, copy_Tr).

    % Check borrowing relationships between RPIL places
    %
    % This can also be used to get the RHS and the kind of a borrow
    %
:- pred ctx_borrowing_check(list(rs_stmt), rpil_op, rpil_op, borrow_kind).
:- mode ctx_borrowing_check(in, in, in, out) is semidet.

ctx_borrowing_check(Stmts, Lhs, Rhs, Kind) :-
    Stmts = [Stmt | StmtsR],
    Stmt = rs_stmt(L, Fn, Args),
    RpilInsts = fn_rpil_reduced(Fn, [L | Args]),
    ctx_borrowing_check_partial(StmtsR, RpilInsts, Lhs, Rhs, Kind),
    ctx_liveness_check(Stmts, origin(Lhs), alive),
    ctx_liveness_check(Stmts, origin(Rhs), alive).
ctx_borrowing_check(Stmts, Lhs, Rhs, Kind) :-
    Stmts = [Stmt | StmtsR],
    Stmt = rs_stmt_uninit(_L),
    ctx_borrowing_check(StmtsR, Lhs, Rhs, Kind).

:- pred ctx_borrowing_check_partial(list(rs_stmt), list(rpil_inst), rpil_op, rpil_op, borrow_kind).
:- mode ctx_borrowing_check_partial(in, in, in, in, out) is semidet.

ctx_borrowing_check_partial(Stmts, [], Lhs, Rhs, Kind) :-
    ctx_borrowing_check(Stmts, Lhs, Rhs, Kind).
ctx_borrowing_check_partial(Stmts, Insts, Lhs, Rhs, Kind) :-
    Insts = [Inst | InstsR],
    ( Inst = rpil_borrow(Lhs, Rhs) ->
        Kind = shared
    ; Inst = rpil_borrow_mut(Lhs, Rhs) ->
        Kind = mutable
    ; Inst = rpil_bind(Lhs, Mid),
      ctx_borrowing_check_partial(Stmts, InstsR, Mid, Rhs, KindR) ->
        Kind = KindR
    ;
        ctx_borrowing_check_partial(Stmts, InstsR, Lhs, Rhs, Kind)
    ).

:- func origin(rpil_op) = int.

origin(arg(_)) =
    unexpected($pred, "cannot determine origin before RPIL reduction").
origin(var(X)) = X.
origin(place(X0, _)) = origin(X0).
origin(place_ext(X0)) = origin(X0).
origin(variant_place(X0, _, _)) = origin(X0).
origin(deref(X0)) = origin(X0).

%---------------------------------------------------------------------------%
%
% Debug utilities: Convert `rs_*' structures to string representations
%

:- func debug_rs_func(rs_func) = string.

debug_rs_func(move_F) = "move".
debug_rs_func(borrow_F) = "&".
debug_rs_func(borrow_mut_F) = "&mut ".
debug_rs_func(store_two_new_F) = "StoreTwo::new".
debug_rs_func(unmovable_new_F) = "Unmovable::new".

:- func debug_rs_type(rs_type) = string.

debug_rs_type(ref_T(T)) =
    string.format("&%s", [s(TR)]) :-
    TR = debug_rs_type(T).
debug_rs_type(mutref_T(T)) =
    string.format("&mut %s", [s(TR)]) :-
    TR = debug_rs_type(T).
debug_rs_type(store_two_T(T1, T2)) =
    string.format("StoreTwo<%s, %s>", [s(T1R), s(T2R)]) :-
    T1R = debug_rs_type(T1),
    T2R = debug_rs_type(T2).
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

debug_rs_stmts(Stmts) = string.join_list("\n", Reprs) :-
    RevReprs = list.map(debug_rs_stmt, Stmts),
    Reprs = list.reverse(RevReprs).

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

debug_rpil_insts(Insts) = string.join_list("\n", Reprs) :-
    Reprs = list.map(debug_rpil_inst, Insts).

:- func debug_liveness(var_liveness) = string.

debug_liveness(alive) = "alive".
debug_liveness(dead) = "dead".

:- func debug_borrow_kind(borrow_kind) = string.

debug_borrow_kind(shared) = "shared".
debug_borrow_kind(mutable) = "mutable".

%---------------------------------------------------------------------------%
:- end_module pinchecker.
%---------------------------------------------------------------------------%

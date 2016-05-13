:- module('thrift_generator', [gen_enum/2, generate/2]).

:- use_module(thrift).

enum_decl(Id, ["type ", Id, " int32"]).
enum_vals([], []).
enum_vals([_:V | Xs], [V:_ | Ys]) :- enum_vals(Xs, Ys).
enum_val_used(V, N, How) :-
    ground(V), findall(U, (member(V:U, N), call(How, U)), [_]).
next_enum_val(V, N, [V1:used | N], V1) :-
    enum_val_used(V, N, ground),
    N = [X:_ | _],
    V1 is X + 1.
next_enum_val(V, N, N, V) :-
    enum_val_used(V, N, var),
    member(V:used, N).
next_enum_val(V, N, [V:used | N], V) :-
    N = [X:_ | _],
    V is X + 1.
enum_consts_body(_, [], _, []).
enum_consts_body(Id, [K:V | Xs], N, [[K1, Id, '=', V1] | Ys]) :-
    next_enum_val(V, N, N1, V1),
    atom_concat(Id, K, K1),
    enum_consts_body(Id, Xs, N1, Ys).
enum_consts(_, [], []).
enum_consts(Id, Entries, ["const (", Body, ")"]) :-
    findall(X, (member(X, Entries), ground(X)), Entries1),
    enum_vals(Entries1, N),
    sort(2, @>, N, N1),
    enum_consts_body(Id, Entries, N1, Body).

enum_serialized(Id, Name, Ser) :-
    atom_concat(Id, '.', X),
    atom_concat(X, Name, Ser).
enum_cases(_, [], []).
enum_cases(Id, [X:_ | Xs], [["case ", X1, ": return \"", X2, "\""] | Ys]) :-
    atom_concat(Id, X, X1),
    enum_serialized(Id, X, X2),
    enum_cases(Id, Xs, Ys).
enum_to_string(Id, Entries, Out) :-
    enum_cases(Id, Entries, Cases),
    Preamble = [["func (e ", Id, ") String() string {"],
                ["switch (e) {"]],
    Postamble = [["}"],
                 ["return fmt.Sprintf(\"Unknown enum value: %d\", e)"],
                 ["}"]],
    append([Preamble, Cases, Postamble], Out).

enum_to_json(Id, Out) :-
    Out = [["func (e ", Id, ") MarshalJSON() ([]byte, error) {"],
           ["return []byte(\"\\\"\" + e.String() + \"\\\"\"), nil"],
           ["}"]].

enum_from_cases(_, [], []).
enum_from_cases(Id, [X:_ | Xs], [["case \"", X2, "\": *e = ", X1], ["return nil"] | Ys]) :-
    atom_concat(Id, X, X1),
    enum_serialized(Id, X, X2),
    enum_from_cases(Id, Xs, Ys).
enum_from_json(Id, Entries, Out) :-
    enum_from_cases(Id, Entries, Cases),
    Preamble = [["func (e *", Id, ") UnmarshalJSON(b []byte) error {"],
                ["s := string(b)"],
                ["switch (s) {"]],
    Postabmle = [["}"],
                 ["return fmt.Errorf(\"Unknown enum member: '%s'\", s)"],
                 ["}"]],
    append([Preamble, Cases, Postabmle], Out).

gen_enum(AST, Out) :-
    enum_id(AST, Id), enum_entries(AST, Entries),
    enum_decl(Id, Decl),
    enum_consts(Id, Entries, Consts),
    enum_to_string(Id, Entries, String),
    enum_to_json(Id, ToJson),
    enum_from_json(Id, Entries, FromJson),
    append([[Decl], Consts, String, ToJson, FromJson], Out).

write_line([]) :- nl.
write_line([X | Xs]) :- write_line(X), write_line(Xs), !.
write_line([X]) :- write(X), !.
write_line(X) :- write(X).

format_lines([], _).
format_lines([X | Xs], Stream) :-
    with_output_to(Stream, (write_line(X), nl)),
    format_lines(Xs, Stream).

generate_all([], _).
generate_all([X | Xs], Stream) :-
    enum_id(X, Id), !,
    format('found enum: ~w~n', [Id]),
    gen_enum(X, Lines),
    format('generated enum: ~w~n', [Id]),
    format_lines(Lines, Stream),
    generate_all(Xs, Stream).
generate_all([X | Xs], Stream) :-
    format('found entry: ~w~n', [X]),
    generate_all(Xs, Stream).

generate(Src, Dst) :-
    parse_file(Src, AST), !,
    doc_header(AST, Header),
    format('header: ~w~n', [Header]),
    doc_body(AST, Body),
    setup_call_cleanup(
        open(Dst, write, S, []),
        generate_all(Body, S),
        close(S)).

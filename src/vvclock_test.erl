-module(vvclock_test).

-compile([export_all]).

%% @doc Run all of the tests.
test() ->
    shallow_test(),
    modified_riak_core_example_test(),
    riak_core_example_test().

%% @doc Generate a test vector clock.
shallow_test() ->
    Fresh = vvclock:fresh(),
    io:format("Fresh: ~p~n", [Fresh]),
    Incremented = vvclock:increment(1, Fresh),
    io:format("Incremented: ~p~n", [Incremented]).

%% @doc Modified riak core example test.
modified_riak_core_example_test() ->
    A  = vvclock:fresh(),
    B  = vvclock:fresh(),
    A1 = vvclock:increment('O', A),
    B1 = vvclock:increment({'S', 'O'}, B),
    B2 = vvclock:increment({'S', 'O'}, B1),

    io:format("A:  ~p~n", [A]),
    io:format("B:  ~p~n", [B]),
    io:format("A1: ~p~n", [A1]),
    io:format("B1: ~p~n", [B1]),
    io:format("B2: ~p~n", [B2]),

    'True'  = vvclock:descends(A1, A),
    'True'  = vvclock:descends(B1, B),
    'False' = vvclock:descends(A1, B1),

    A2 = vvclock:increment('O', A1),
    C  = vvclock:merge(A2, B1),
    C1 = vvclock:increment({'S', {'S', 'O'}}, C),

    io:format("A2: ~p~n", [A2]),
    io:format("C:  ~p~n",  [C]),
    io:format("C1: ~p~n", [C1]),

    'True'  = vvclock:descends(C1, A2),
    'True'  = vvclock:descends(C1, B1),
    'False' = vvclock:descends(B1, C1),
    'False' = vvclock:descends(B1, A1),

    ok.

%% @doc Riak Core example test.
riak_core_example_test() ->
    A = vclock:fresh(),
    B = vclock:fresh(),
    A1 = vclock:increment(a, A),
    B1 = vclock:increment(b, B),
    true = vclock:descends(A1,A),
    true = vclock:descends(B1,B),
    false = vclock:descends(A1,B1),
    A2 = vclock:increment(a, A1),
    C = vclock:merge([A2, B1]),
    C1 = vclock:increment(c, C),
    true = vclock:descends(C1, A2),
    true = vclock:descends(C1, B1),
    false = vclock:descends(B1, C1),
    false = vclock:descends(B1, A1),
    ok.
